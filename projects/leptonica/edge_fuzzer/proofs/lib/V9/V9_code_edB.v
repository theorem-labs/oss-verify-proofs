(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushU9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_63624 : bv 32 := 0x00050a63.
Lemma F_63624 : fetch_word Ubsan.M.loaded_segments (0x6367c : word) = Some W_63624.
Proof. vm_refl. Qed.
Lemma D_63624 : decode_any W_63624 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63628 : bv 32 := 0x00757593.
Lemma F_63628 : fetch_word Ubsan.M.loaded_segments (0x63680 : word) = Some W_63628.
Proof. vm_refl. Qed.
Lemma D_63628 : decode_any W_63628 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6362c : bv 32 := 0x04059063.
Lemma F_6362c : fetch_word Ubsan.M.loaded_segments (0x63684 : word) = Some W_6362c.
Proof. vm_refl. Qed.
Lemma D_6362c : decode_any W_6362c = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63630 : bv 32 := 0x01052503.
Lemma F_63630 : fetch_word Ubsan.M.loaded_segments (0x63688 : word) = Some W_63630.
Proof. vm_refl. Qed.
Lemma D_63630 : decode_any W_63630 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63634 : bv 32 := 0x00008067.
Lemma F_63634 : fetch_word Ubsan.M.loaded_segments (0x6368c : word) = Some W_63634.
Proof. vm_refl. Qed.
Lemma D_63634 : decode_any W_63634 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6397c : bv 32 := 0x0035f713.
Lemma F_6397c : fetch_word Ubsan.M.loaded_segments (0x639d4 : word) = Some W_6397c.
Proof. vm_refl. Qed.
Lemma D_6397c : decode_any W_6397c = Some (OpImm ALU_AND 14 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63980 : bv 32 := 0x00058663.
Lemma F_63980 : fetch_word Ubsan.M.loaded_segments (0x639d8 : word) = Some W_63980.
Proof. vm_refl. Qed.
Lemma D_63980 : decode_any W_63980 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63984 : bv 32 := 0x0a071863.
Lemma F_63984 : fetch_word Ubsan.M.loaded_segments (0x639dc : word) = Some W_63984.
Proof. vm_refl. Qed.
Lemma D_63984 : decode_any W_63984 = Some (Branch BC_NE 14 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63988 : bv 32 := 0x0005a023.
Lemma F_63988 : fetch_word Ubsan.M.loaded_segments (0x639e0 : word) = Some W_63988.
Proof. vm_refl. Qed.
Lemma D_63988 : decode_any W_63988 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6398c : bv 32 := 0x00367793.
Lemma F_6398c : fetch_word Ubsan.M.loaded_segments (0x639e4 : word) = Some W_6398c.
Proof. vm_refl. Qed.
Lemma D_6398c : decode_any W_6398c = Some (OpImm ALU_AND 15 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63990 : bv 32 := 0x00060663.
Lemma F_63990 : fetch_word Ubsan.M.loaded_segments (0x639e8 : word) = Some W_63990.
Proof. vm_refl. Qed.
Lemma D_63990 : decode_any W_63990 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63994 : bv 32 := 0x0a079063.
Lemma F_63994 : fetch_word Ubsan.M.loaded_segments (0x639ec : word) = Some W_63994.
Proof. vm_refl. Qed.
Lemma D_63994 : decode_any W_63994 = Some (Branch BC_NE 15 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63998 : bv 32 := 0x00062023.
Lemma F_63998 : fetch_word Ubsan.M.loaded_segments (0x639f0 : word) = Some W_63998.
Proof. vm_refl. Qed.
Lemma D_63998 : decode_any W_63998 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6399c : bv 32 := 0x0036f813.
Lemma F_6399c : fetch_word Ubsan.M.loaded_segments (0x639f4 : word) = Some W_6399c.
Proof. vm_refl. Qed.
Lemma D_6399c : decode_any W_6399c = Some (OpImm ALU_AND 16 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639a0 : bv 32 := 0x00068663.
Lemma F_639a0 : fetch_word Ubsan.M.loaded_segments (0x639f8 : word) = Some W_639a0.
Proof. vm_refl. Qed.
Lemma D_639a0 : decode_any W_639a0 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639a4 : bv 32 := 0x08081863.
Lemma F_639a4 : fetch_word Ubsan.M.loaded_segments (0x639fc : word) = Some W_639a4.
Proof. vm_refl. Qed.
Lemma D_639a4 : decode_any W_639a4 = Some (Branch BC_NE 16 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639a8 : bv 32 := 0x0006a023.
Lemma F_639a8 : fetch_word Ubsan.M.loaded_segments (0x63a00 : word) = Some W_639a8.
Proof. vm_refl. Qed.
Lemma D_639a8 : decode_any W_639a8 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639ac : bv 32 := 0x04050663.
Lemma F_639ac : fetch_word Ubsan.M.loaded_segments (0x63a04 : word) = Some W_639ac.
Proof. vm_refl. Qed.
Lemma D_639ac : decode_any W_639ac = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639b0 : bv 32 := 0x00757893.
Lemma F_639b0 : fetch_word Ubsan.M.loaded_segments (0x63a08 : word) = Some W_639b0.
Proof. vm_refl. Qed.
Lemma D_639b0 : decode_any W_639b0 = Some (OpImm ALU_AND 17 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639b4 : bv 32 := 0x00058a63.
Lemma F_639b4 : fetch_word Ubsan.M.loaded_segments (0x63a0c : word) = Some W_639b4.
Proof. vm_refl. Qed.
Lemma D_639b4 : decode_any W_639b4 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639b8 : bv 32 := 0x00e8e733.
Lemma F_639b8 : fetch_word Ubsan.M.loaded_segments (0x63a10 : word) = Some W_639b8.
Proof. vm_refl. Qed.
Lemma D_639b8 : decode_any W_639b8 = Some (Op ALU_OR 14 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639bc : bv 32 := 0x06071c63.
Lemma F_639bc : fetch_word Ubsan.M.loaded_segments (0x63a14 : word) = Some W_639bc.
Proof. vm_refl. Qed.
Lemma D_639bc : decode_any W_639bc = Some (Branch BC_NE 14 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639c0 : bv 32 := 0x00052703.
Lemma F_639c0 : fetch_word Ubsan.M.loaded_segments (0x63a18 : word) = Some W_639c0.
Proof. vm_refl. Qed.
Lemma D_639c0 : decode_any W_639c0 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639c4 : bv 32 := 0x00e5a023.
Lemma F_639c4 : fetch_word Ubsan.M.loaded_segments (0x63a1c : word) = Some W_639c4.
Proof. vm_refl. Qed.
Lemma D_639c4 : decode_any W_639c4 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639c8 : bv 32 := 0x00060a63.
Lemma F_639c8 : fetch_word Ubsan.M.loaded_segments (0x63a20 : word) = Some W_639c8.
Proof. vm_refl. Qed.
Lemma D_639c8 : decode_any W_639c8 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639cc : bv 32 := 0x00f8e5b3.
Lemma F_639cc : fetch_word Ubsan.M.loaded_segments (0x63a24 : word) = Some W_639cc.
Proof. vm_refl. Qed.
Lemma D_639cc : decode_any W_639cc = Some (Op ALU_OR 11 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639d0 : bv 32 := 0x06059263.
Lemma F_639d0 : fetch_word Ubsan.M.loaded_segments (0x63a28 : word) = Some W_639d0.
Proof. vm_refl. Qed.
Lemma D_639d0 : decode_any W_639d0 = Some (Branch BC_NE 11 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639d4 : bv 32 := 0x00452583.
Lemma F_639d4 : fetch_word Ubsan.M.loaded_segments (0x63a2c : word) = Some W_639d4.
Proof. vm_refl. Qed.
Lemma D_639d4 : decode_any W_639d4 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639d8 : bv 32 := 0x00b62023.
Lemma F_639d8 : fetch_word Ubsan.M.loaded_segments (0x63a30 : word) = Some W_639d8.
Proof. vm_refl. Qed.
Lemma D_639d8 : decode_any W_639d8 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639dc : bv 32 := 0x04068463.
Lemma F_639dc : fetch_word Ubsan.M.loaded_segments (0x63a34 : word) = Some W_639dc.
Proof. vm_refl. Qed.
Lemma D_639dc : decode_any W_639dc = Some (Branch BC_EQ 13 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639e0 : bv 32 := 0x0108e5b3.
Lemma F_639e0 : fetch_word Ubsan.M.loaded_segments (0x63a38 : word) = Some W_639e0.
Proof. vm_refl. Qed.
Lemma D_639e0 : decode_any W_639e0 = Some (Op ALU_OR 11 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639e4 : bv 32 := 0x04059863.
Lemma F_639e4 : fetch_word Ubsan.M.loaded_segments (0x63a3c : word) = Some W_639e4.
Proof. vm_refl. Qed.
Lemma D_639e4 : decode_any W_639e4 = Some (Branch BC_NE 11 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639e8 : bv 32 := 0x00852503.
Lemma F_639e8 : fetch_word Ubsan.M.loaded_segments (0x63a40 : word) = Some W_639e8.
Proof. vm_refl. Qed.
Lemma D_639e8 : decode_any W_639e8 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639ec : bv 32 := 0x00a6a023.
Lemma F_639ec : fetch_word Ubsan.M.loaded_segments (0x63a44 : word) = Some W_639ec.
Proof. vm_refl. Qed.
Lemma D_639ec : decode_any W_639ec = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639f0 : bv 32 := 0x00058513.
Lemma F_639f0 : fetch_word Ubsan.M.loaded_segments (0x63a48 : word) = Some W_639f0.
Proof. vm_refl. Qed.
Lemma D_639f0 : decode_any W_639f0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639f4 : bv 32 := 0x00008067.
Lemma F_639f4 : fetch_word Ubsan.M.loaded_segments (0x63a4c : word) = Some W_639f4.
Proof. vm_refl. Qed.
Lemma D_639f4 : decode_any W_639f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a24 : bv 32 := 0x00000513.
Lemma F_63a24 : fetch_word Ubsan.M.loaded_segments (0x63a7c : word) = Some W_63a24.
Proof. vm_refl. Qed.
Lemma D_63a24 : decode_any W_63a24 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a28 : bv 32 := 0x00008067.
Lemma F_63a28 : fetch_word Ubsan.M.loaded_segments (0x63a80 : word) = Some W_63a28.
Proof. vm_refl. Qed.
Lemma D_63a28 : decode_any W_63a28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_645dc : bv 32 := 0x00050a63.
Lemma F_645dc : fetch_word Ubsan.M.loaded_segments (0x64634 : word) = Some W_645dc.
Proof. vm_refl. Qed.
Lemma D_645dc : decode_any W_645dc = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_645e0 : bv 32 := 0x00757593.
Lemma F_645e0 : fetch_word Ubsan.M.loaded_segments (0x64638 : word) = Some W_645e0.
Proof. vm_refl. Qed.
Lemma D_645e0 : decode_any W_645e0 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_645e4 : bv 32 := 0x04059063.
Lemma F_645e4 : fetch_word Ubsan.M.loaded_segments (0x6463c : word) = Some W_645e4.
Proof. vm_refl. Qed.
Lemma D_645e4 : decode_any W_645e4 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_645e8 : bv 32 := 0x00852503.
Lemma F_645e8 : fetch_word Ubsan.M.loaded_segments (0x64640 : word) = Some W_645e8.
Proof. vm_refl. Qed.
Lemma D_645e8 : decode_any W_645e8 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_645ec : bv 32 := 0x00008067.
Lemma F_645ec : fetch_word Ubsan.M.loaded_segments (0x64644 : word) = Some W_645ec.
Proof. vm_refl. Qed.
Lemma D_645ec : decode_any W_645ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_646b4 : bv 32 := 0x00050a63.
Lemma F_646b4 : fetch_word Ubsan.M.loaded_segments (0x6470c : word) = Some W_646b4.
Proof. vm_refl. Qed.
Lemma D_646b4 : decode_any W_646b4 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_646b8 : bv 32 := 0x00757593.
Lemma F_646b8 : fetch_word Ubsan.M.loaded_segments (0x64710 : word) = Some W_646b8.
Proof. vm_refl. Qed.
Lemma D_646b8 : decode_any W_646b8 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_646bc : bv 32 := 0x04059063.
Lemma F_646bc : fetch_word Ubsan.M.loaded_segments (0x64714 : word) = Some W_646bc.
Proof. vm_refl. Qed.
Lemma D_646bc : decode_any W_646bc = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_646c0 : bv 32 := 0x03853503.
Lemma F_646c0 : fetch_word Ubsan.M.loaded_segments (0x64718 : word) = Some W_646c0.
Proof. vm_refl. Qed.
Lemma D_646c0 : decode_any W_646c0 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_646c4 : bv 32 := 0x00008067.
Lemma F_646c4 : fetch_word Ubsan.M.loaded_segments (0x6471c : word) = Some W_646c4.
Proof. vm_refl. Qed.
Lemma D_646c4 : decode_any W_646c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64914 : bv 32 := 0xfc010113.
Lemma F_64914 : fetch_word Ubsan.M.loaded_segments (0x6496c : word) = Some W_64914.
Proof. vm_refl. Qed.
Lemma D_64914 : decode_any W_64914 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64918 : bv 32 := 0x02113c23.
Lemma F_64918 : fetch_word Ubsan.M.loaded_segments (0x64970 : word) = Some W_64918.
Proof. vm_refl. Qed.
Lemma D_64918 : decode_any W_64918 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6491c : bv 32 := 0x02813823.
Lemma F_6491c : fetch_word Ubsan.M.loaded_segments (0x64974 : word) = Some W_6491c.
Proof. vm_refl. Qed.
Lemma D_6491c : decode_any W_6491c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64920 : bv 32 := 0x02913423.
Lemma F_64920 : fetch_word Ubsan.M.loaded_segments (0x64978 : word) = Some W_64920.
Proof. vm_refl. Qed.
Lemma D_64920 : decode_any W_64920 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64924 : bv 32 := 0x03213023.
Lemma F_64924 : fetch_word Ubsan.M.loaded_segments (0x6497c : word) = Some W_64924.
Proof. vm_refl. Qed.
Lemma D_64924 : decode_any W_64924 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64928 : bv 32 := 0x01313c23.
Lemma F_64928 : fetch_word Ubsan.M.loaded_segments (0x64980 : word) = Some W_64928.
Proof. vm_refl. Qed.
Lemma D_64928 : decode_any W_64928 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6492c : bv 32 := 0x01413823.
Lemma F_6492c : fetch_word Ubsan.M.loaded_segments (0x64984 : word) = Some W_6492c.
Proof. vm_refl. Qed.
Lemma D_6492c : decode_any W_6492c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64930 : bv 32 := 0x10068463.
Lemma F_64930 : fetch_word Ubsan.M.loaded_segments (0x64988 : word) = Some W_64930.
Proof. vm_refl. Qed.
Lemma D_64930 : decode_any W_64930 = Some (Branch BC_EQ 13 0 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64934 : bv 32 := 0x00058413.
Lemma F_64934 : fetch_word Ubsan.M.loaded_segments (0x6498c : word) = Some W_64934.
Proof. vm_refl. Qed.
Lemma D_64934 : decode_any W_64934 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64938 : bv 32 := 0x0036f593.
Lemma F_64938 : fetch_word Ubsan.M.loaded_segments (0x64990 : word) = Some W_64938.
Proof. vm_refl. Qed.
Lemma D_64938 : decode_any W_64938 = Some (OpImm ALU_AND 11 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6493c : bv 32 := 0x2c059e63.
Lemma F_6493c : fetch_word Ubsan.M.loaded_segments (0x64994 : word) = Some W_6493c.
Proof. vm_refl. Qed.
Lemma D_6493c : decode_any W_6493c = Some (Branch BC_NE 11 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64940 : bv 32 := 0x0006a023.
Lemma F_64940 : fetch_word Ubsan.M.loaded_segments (0x64998 : word) = Some W_64940.
Proof. vm_refl. Qed.
Lemma D_64940 : decode_any W_64940 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64944 : bv 32 := 0x10050e63.
Lemma F_64944 : fetch_word Ubsan.M.loaded_segments (0x6499c : word) = Some W_64944.
Proof. vm_refl. Qed.
Lemma D_64944 : decode_any W_64944 = Some (Branch BC_EQ 10 0 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64948 : bv 32 := 0x00060493.
Lemma F_64948 : fetch_word Ubsan.M.loaded_segments (0x649a0 : word) = Some W_64948.
Proof. vm_refl. Qed.
Lemma D_64948 : decode_any W_64948 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6494c : bv 32 := 0x00068a13.
Lemma F_6494c : fetch_word Ubsan.M.loaded_segments (0x649a4 : word) = Some W_6494c.
Proof. vm_refl. Qed.
Lemma D_6494c : decode_any W_6494c = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64950 : bv 32 := 0x00c10593.
Lemma F_64950 : fetch_word Ubsan.M.loaded_segments (0x649a8 : word) = Some W_64950.
Proof. vm_refl. Qed.
Lemma D_64950 : decode_any W_64950 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64954 : bv 32 := 0x00810613.
Lemma F_64954 : fetch_word Ubsan.M.loaded_segments (0x649ac : word) = Some W_64954.
Proof. vm_refl. Qed.
Lemma D_64954 : decode_any W_64954 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64958 : bv 32 := 0x00410693.
Lemma F_64958 : fetch_word Ubsan.M.loaded_segments (0x649b0 : word) = Some W_64958.
Proof. vm_refl. Qed.
Lemma D_64958 : decode_any W_64958 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6495c : bv 32 := 0x00050913.
Lemma F_6495c : fetch_word Ubsan.M.loaded_segments (0x649b4 : word) = Some W_6495c.
Proof. vm_refl. Qed.
Lemma D_6495c : decode_any W_6495c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64960 : bv 32 := 0x81cff0ef.
Lemma F_64960 : fetch_word Ubsan.M.loaded_segments (0x649b8 : word) = Some W_64960.
Proof. vm_refl. Qed.
Lemma D_64960 : decode_any W_64960 = Some (Jal 1 2093084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64964 : bv 32 := 0x00200513.
Lemma F_64964 : fetch_word Ubsan.M.loaded_segments (0x649bc : word) = Some W_64964.
Proof. vm_refl. Qed.
Lemma D_64964 : decode_any W_64964 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64968 : bv 32 := 0x28044863.
Lemma F_64968 : fetch_word Ubsan.M.loaded_segments (0x649c0 : word) = Some W_64968.
Proof. vm_refl. Qed.
Lemma D_64968 : decode_any W_64968 = Some (Branch BC_LT 8 0 656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6496c : bv 32 := 0x2804c663.
Lemma F_6496c : fetch_word Ubsan.M.loaded_segments (0x649c4 : word) = Some W_6496c.
Proof. vm_refl. Qed.
Lemma D_6496c : decode_any W_6496c = Some (Branch BC_LT 9 0 652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64970 : bv 32 := 0x00c12583.
Lemma F_64970 : fetch_word Ubsan.M.loaded_segments (0x649c8 : word) = Some W_64970.
Proof. vm_refl. Qed.
Lemma D_64970 : decode_any W_64970 = Some (Load SZ4 true 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64974 : bv 32 := 0x28b45263.
Lemma F_64974 : fetch_word Ubsan.M.loaded_segments (0x649cc : word) = Some W_64974.
Proof. vm_refl. Qed.
Lemma D_64974 : decode_any W_64974 = Some (Branch BC_GE 8 11 644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64978 : bv 32 := 0x00812583.
Lemma F_64978 : fetch_word Ubsan.M.loaded_segments (0x649d0 : word) = Some W_64978.
Proof. vm_refl. Qed.
Lemma D_64978 : decode_any W_64978 = Some (Load SZ4 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6497c : bv 32 := 0x26b4de63.
Lemma F_6497c : fetch_word Ubsan.M.loaded_segments (0x649d4 : word) = Some W_6497c.
Proof. vm_refl. Qed.
Lemma D_6497c : decode_any W_6497c = Some (Branch BC_GE 9 11 636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64980 : bv 32 := 0x00090513.
Lemma F_64980 : fetch_word Ubsan.M.loaded_segments (0x649d8 : word) = Some W_64980.
Proof. vm_refl. Qed.
Lemma D_64980 : decode_any W_64980 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64984 : bv 32 := 0xca1fe0ef.
Lemma F_64984 : fetch_word Ubsan.M.loaded_segments (0x649dc : word) = Some W_64984.
Proof. vm_refl. Qed.
Lemma D_64984 : decode_any W_64984 = Some (Jal 1 2092192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64988 : bv 32 := 0x00050993.
Lemma F_64988 : fetch_word Ubsan.M.loaded_segments (0x649e0 : word) = Some W_64988.
Proof. vm_refl. Qed.
Lemma D_64988 : decode_any W_64988 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6498c : bv 32 := 0x00090513.
Lemma F_6498c : fetch_word Ubsan.M.loaded_segments (0x649e4 : word) = Some W_6498c.
Proof. vm_refl. Qed.
Lemma D_6498c : decode_any W_6498c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64990 : bv 32 := 0xd25ff0ef.
Lemma F_64990 : fetch_word Ubsan.M.loaded_segments (0x649e8 : word) = Some W_64990.
Proof. vm_refl. Qed.
Lemma D_64990 : decode_any W_64990 = Some (Jal 1 2096420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64994 : bv 32 := 0x03348733.
Lemma F_64994 : fetch_word Ubsan.M.loaded_segments (0x649ec : word) = Some W_64994.
Proof. vm_refl. Qed.
Lemma D_64994 : decode_any W_64994 = Some (Mul M_MUL 14 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64998 : bv 32 := 0x033485bb.
Lemma F_64998 : fetch_word Ubsan.M.loaded_segments (0x649f0 : word) = Some W_64998.
Proof. vm_refl. Qed.
Lemma D_64998 : decode_any W_64998 = Some (Mul32 M_MUL 11 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6499c : bv 32 := 0x26e59e63.
Lemma F_6499c : fetch_word Ubsan.M.loaded_segments (0x649f4 : word) = Some W_6499c.
Proof. vm_refl. Qed.
Lemma D_6499c : decode_any W_6499c = Some (Branch BC_NE 11 14 636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649a0 : bv 32 := 0x0007071b.
Lemma F_649a0 : fetch_word Ubsan.M.loaded_segments (0x649f8 : word) = Some W_649a0.
Proof. vm_refl. Qed.
Lemma D_649a0 : decode_any W_649a0 = Some (OpImm32 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649a4 : bv 32 := 0x00271693.
Lemma F_649a4 : fetch_word Ubsan.M.loaded_segments (0x649fc : word) = Some W_649a4.
Proof. vm_refl. Qed.
Lemma D_649a4 : decode_any W_649a4 = Some (ShiftImm ALU_SLL 13 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649a8 : bv 32 := 0x00d506b3.
Lemma F_649a8 : fetch_word Ubsan.M.loaded_segments (0x64a00 : word) = Some W_649a8.
Proof. vm_refl. Qed.
Lemma D_649a8 : decode_any W_649a8 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649ac : bv 32 := 0x00a03633.
Lemma F_649ac : fetch_word Ubsan.M.loaded_segments (0x64a04 : word) = Some W_649ac.
Proof. vm_refl. Qed.
Lemma D_649ac : decode_any W_649ac = Some (Op ALU_SLTU 12 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649b0 : bv 32 := 0x0016b793.
Lemma F_649b0 : fetch_word Ubsan.M.loaded_segments (0x64a08 : word) = Some W_649b0.
Proof. vm_refl. Qed.
Lemma D_649b0 : decode_any W_649b0 = Some (OpImm ALU_SLTU 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649b4 : bv 32 := 0x26f60263.
Lemma F_649b4 : fetch_word Ubsan.M.loaded_segments (0x64a0c : word) = Some W_649b4.
Proof. vm_refl. Qed.
Lemma D_649b4 : decode_any W_649b4 = Some (Branch BC_EQ 12 15 612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649b8 : bv 32 := 0x00a6b7b3.
Lemma F_649b8 : fetch_word Ubsan.M.loaded_segments (0x64a10 : word) = Some W_649b8.
Proof. vm_refl. Qed.
Lemma D_649b8 : decode_any W_649b8 = Some (Op ALU_SLTU 15 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649bc : bv 32 := 0x00072713.
Lemma F_649bc : fetch_word Ubsan.M.loaded_segments (0x64a14 : word) = Some W_649bc.
Proof. vm_refl. Qed.
Lemma D_649bc : decode_any W_649bc = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649c0 : bv 32 := 0x00e7c733.
Lemma F_649c0 : fetch_word Ubsan.M.loaded_segments (0x64a18 : word) = Some W_649c0.
Proof. vm_refl. Qed.
Lemma D_649c0 : decode_any W_649c0 = Some (Op ALU_XOR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649c4 : bv 32 := 0x00174713.
Lemma F_649c4 : fetch_word Ubsan.M.loaded_segments (0x64a1c : word) = Some W_649c4.
Proof. vm_refl. Qed.
Lemma D_649c4 : decode_any W_649c4 = Some (OpImm ALU_XOR 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649c8 : bv 32 := 0x24070863.
Lemma F_649c8 : fetch_word Ubsan.M.loaded_segments (0x64a20 : word) = Some W_649c8.
Proof. vm_refl. Qed.
Lemma D_649c8 : decode_any W_649c8 = Some (Branch BC_EQ 14 0 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649cc : bv 32 := 0x00412703.
Lemma F_649cc : fetch_word Ubsan.M.loaded_segments (0x64a24 : word) = Some W_649cc.
Proof. vm_refl. Qed.
Lemma D_649cc : decode_any W_649cc = Some (Load SZ4 true 14 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649d0 : bv 32 := 0xfff70713.
Lemma F_649d0 : fetch_word Ubsan.M.loaded_segments (0x64a28 : word) = Some W_649d0.
Proof. vm_refl. Qed.
Lemma D_649d0 : decode_any W_649d0 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649d4 : bv 32 := 0x01f00793.
Lemma F_649d4 : fetch_word Ubsan.M.loaded_segments (0x64a2c : word) = Some W_649d4.
Proof. vm_refl. Qed.
Lemma D_649d4 : decode_any W_649d4 = Some (OpImm ALU_ADD 15 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649d8 : bv 32 := 0x12e7ee63.
Lemma F_649d8 : fetch_word Ubsan.M.loaded_segments (0x64a30 : word) = Some W_649d8.
Proof. vm_refl. Qed.
Lemma D_649d8 : decode_any W_649d8 = Some (Branch BC_LTU 15 14 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649dc : bv 32 := 0x000a0593.
Lemma F_649dc : fetch_word Ubsan.M.loaded_segments (0x64a34 : word) = Some W_649dc.
Proof. vm_refl. Qed.
Lemma D_649dc : decode_any W_649dc = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649e0 : bv 32 := 0x00271713.
Lemma F_649e0 : fetch_word Ubsan.M.loaded_segments (0x64a38 : word) = Some W_649e0.
Proof. vm_refl. Qed.
Lemma D_649e0 : decode_any W_649e0 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649e4 : bv 32 := 0xfffb8797.
Lemma F_649e4 : fetch_word Ubsan.M.loaded_segments (0x64a3c : word) = Some W_649e4.
Proof. vm_refl. Qed.
Lemma D_649e4 : decode_any W_649e4 = Some (Auipc 15 1048504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649e8 : bv 32 := 0xcd078793.
Lemma F_649e8 : fetch_word Ubsan.M.loaded_segments (0x64a40 : word) = Some W_649e8.
Proof. vm_refl. Qed.
Lemma D_649e8 : decode_any W_649e8 = Some (OpImm ALU_ADD 15 15 3280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649ec : bv 32 := 0x00f70733.
Lemma F_649ec : fetch_word Ubsan.M.loaded_segments (0x64a44 : word) = Some W_649ec.
Proof. vm_refl. Qed.
Lemma D_649ec : decode_any W_649ec = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649f0 : bv 32 := 0x00072703.
Lemma F_649f0 : fetch_word Ubsan.M.loaded_segments (0x64a48 : word) = Some W_649f0.
Proof. vm_refl. Qed.
Lemma D_649f0 : decode_any W_649f0 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649f4 : bv 32 := 0x00f70733.
Lemma F_649f4 : fetch_word Ubsan.M.loaded_segments (0x64a4c : word) = Some W_649f4.
Proof. vm_refl. Qed.
Lemma D_649f4 : decode_any W_649f4 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649f8 : bv 32 := 0x00070067.
Lemma F_649f8 : fetch_word Ubsan.M.loaded_segments (0x64a50 : word) = Some W_649f8.
Proof. vm_refl. Qed.
Lemma D_649f8 : decode_any W_649f8 = Some (Jalr 0 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_649fc : bv 32 := 0x0054571b.
Lemma F_649fc : fetch_word Ubsan.M.loaded_segments (0x64a54 : word) = Some W_649fc.
Proof. vm_refl. Qed.
Lemma D_649fc : decode_any W_649fc = Some (ShiftImm32 ALU_SRL 14 8 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a00 : bv 32 := 0x00271713.
Lemma F_64a00 : fetch_word Ubsan.M.loaded_segments (0x64a58 : word) = Some W_64a00.
Proof. vm_refl. Qed.
Lemma D_64a00 : decode_any W_64a00 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a04 : bv 32 := 0x00e68733.
Lemma F_64a04 : fetch_word Ubsan.M.loaded_segments (0x64a5c : word) = Some W_64a04.
Proof. vm_refl. Qed.
Lemma D_64a04 : decode_any W_64a04 = Some (Op ALU_ADD 14 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a08 : bv 32 := 0x20d76863.
Lemma F_64a08 : fetch_word Ubsan.M.loaded_segments (0x64a60 : word) = Some W_64a08.
Proof. vm_refl. Qed.
Lemma D_64a08 : decode_any W_64a08 = Some (Branch BC_LTU 14 13 528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a0c : bv 32 := 0x00173693.
Lemma F_64a0c : fetch_word Ubsan.M.loaded_segments (0x64a64 : word) = Some W_64a0c.
Proof. vm_refl. Qed.
Lemma D_64a0c : decode_any W_64a0c = Some (OpImm ALU_SLTU 13 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a10 : bv 32 := 0x00d64633.
Lemma F_64a10 : fetch_word Ubsan.M.loaded_segments (0x64a68 : word) = Some W_64a10.
Proof. vm_refl. Qed.
Lemma D_64a10 : decode_any W_64a10 = Some (Op ALU_XOR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a14 : bv 32 := 0x20060263.
Lemma F_64a14 : fetch_word Ubsan.M.loaded_segments (0x64a6c : word) = Some W_64a14.
Proof. vm_refl. Qed.
Lemma D_64a14 : decode_any W_64a14 = Some (Branch BC_EQ 12 0 516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a18 : bv 32 := 0x20050063.
Lemma F_64a18 : fetch_word Ubsan.M.loaded_segments (0x64a70 : word) = Some W_64a18.
Proof. vm_refl. Qed.
Lemma D_64a18 : decode_any W_64a18 = Some (Branch BC_EQ 10 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a1c : bv 32 := 0x00377513.
Lemma F_64a1c : fetch_word Ubsan.M.loaded_segments (0x64a74 : word) = Some W_64a1c.
Proof. vm_refl. Qed.
Lemma D_64a1c : decode_any W_64a1c = Some (OpImm ALU_AND 10 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a20 : bv 32 := 0x1e051c63.
Lemma F_64a20 : fetch_word Ubsan.M.loaded_segments (0x64a78 : word) = Some W_64a20.
Proof. vm_refl. Qed.
Lemma D_64a20 : decode_any W_64a20 = Some (Branch BC_NE 10 0 504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a24 : bv 32 := 0x00072503.
Lemma F_64a24 : fetch_word Ubsan.M.loaded_segments (0x64a7c : word) = Some W_64a24.
Proof. vm_refl. Qed.
Lemma D_64a24 : decode_any W_64a24 = Some (Load SZ4 true 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a28 : bv 32 := 0xfff44613.
Lemma F_64a28 : fetch_word Ubsan.M.loaded_segments (0x64a80 : word) = Some W_64a28.
Proof. vm_refl. Qed.
Lemma D_64a28 : decode_any W_64a28 = Some (OpImm ALU_XOR 12 8 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a2c : bv 32 := 0x00c5563b.
Lemma F_64a2c : fetch_word Ubsan.M.loaded_segments (0x64a84 : word) = Some W_64a2c.
Proof. vm_refl. Qed.
Lemma D_64a2c : decode_any W_64a2c = Some (Op32 ALU_SRL 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a30 : bv 32 := 0x00167613.
Lemma F_64a30 : fetch_word Ubsan.M.loaded_segments (0x64a88 : word) = Some W_64a30.
Proof. vm_refl. Qed.
Lemma D_64a30 : decode_any W_64a30 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64a34 : bv 32 := 0x1bc0006f.
Lemma F_64a34 : fetch_word Ubsan.M.loaded_segments (0x64a8c : word) = Some W_64a34.
Proof. vm_refl. Qed.
Lemma D_64a34 : decode_any W_64a34 = Some (Jal 0 444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64bf0 : bv 32 := 0x00000513.
Lemma F_64bf0 : fetch_word Ubsan.M.loaded_segments (0x64c48 : word) = Some W_64bf0.
Proof. vm_refl. Qed.
Lemma D_64bf0 : decode_any W_64bf0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64bf4 : bv 32 := 0x00c5a023.
Lemma F_64bf4 : fetch_word Ubsan.M.loaded_segments (0x64c4c : word) = Some W_64bf4.
Proof. vm_refl. Qed.
Lemma D_64bf4 : decode_any W_64bf4 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64bf8 : bv 32 := 0x03813083.
Lemma F_64bf8 : fetch_word Ubsan.M.loaded_segments (0x64c50 : word) = Some W_64bf8.
Proof. vm_refl. Qed.
Lemma D_64bf8 : decode_any W_64bf8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64bfc : bv 32 := 0x03013403.
Lemma F_64bfc : fetch_word Ubsan.M.loaded_segments (0x64c54 : word) = Some W_64bfc.
Proof. vm_refl. Qed.
Lemma D_64bfc : decode_any W_64bfc = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c00 : bv 32 := 0x02813483.
Lemma F_64c00 : fetch_word Ubsan.M.loaded_segments (0x64c58 : word) = Some W_64c00.
Proof. vm_refl. Qed.
Lemma D_64c00 : decode_any W_64c00 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c04 : bv 32 := 0x02013903.
Lemma F_64c04 : fetch_word Ubsan.M.loaded_segments (0x64c5c : word) = Some W_64c04.
Proof. vm_refl. Qed.
Lemma D_64c04 : decode_any W_64c04 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c08 : bv 32 := 0x01813983.
Lemma F_64c08 : fetch_word Ubsan.M.loaded_segments (0x64c60 : word) = Some W_64c08.
Proof. vm_refl. Qed.
Lemma D_64c08 : decode_any W_64c08 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c0c : bv 32 := 0x01013a03.
Lemma F_64c0c : fetch_word Ubsan.M.loaded_segments (0x64c64 : word) = Some W_64c0c.
Proof. vm_refl. Qed.
Lemma D_64c0c : decode_any W_64c0c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c10 : bv 32 := 0x04010113.
Lemma F_64c10 : fetch_word Ubsan.M.loaded_segments (0x64c68 : word) = Some W_64c10.
Proof. vm_refl. Qed.
Lemma D_64c10 : decode_any W_64c10 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c14 : bv 32 := 0x00008067.
Lemma F_64c14 : fetch_word Ubsan.M.loaded_segments (0x64c6c : word) = Some W_64c14.
Proof. vm_refl. Qed.
Lemma D_64c14 : decode_any W_64c14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82710 : bv 32 := 0xfa010113.
Lemma F_82710 : fetch_word Ubsan.M.loaded_segments (0x82768 : word) = Some W_82710.
Proof. vm_refl. Qed.
Lemma D_82710 : decode_any W_82710 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82714 : bv 32 := 0x04113c23.
Lemma F_82714 : fetch_word Ubsan.M.loaded_segments (0x8276c : word) = Some W_82714.
Proof. vm_refl. Qed.
Lemma D_82714 : decode_any W_82714 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82718 : bv 32 := 0x04813823.
Lemma F_82718 : fetch_word Ubsan.M.loaded_segments (0x82770 : word) = Some W_82718.
Proof. vm_refl. Qed.
Lemma D_82718 : decode_any W_82718 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8271c : bv 32 := 0x04913423.
Lemma F_8271c : fetch_word Ubsan.M.loaded_segments (0x82774 : word) = Some W_8271c.
Proof. vm_refl. Qed.
Lemma D_8271c : decode_any W_8271c = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82720 : bv 32 := 0x05213023.
Lemma F_82720 : fetch_word Ubsan.M.loaded_segments (0x82778 : word) = Some W_82720.
Proof. vm_refl. Qed.
Lemma D_82720 : decode_any W_82720 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82724 : bv 32 := 0x03313c23.
Lemma F_82724 : fetch_word Ubsan.M.loaded_segments (0x8277c : word) = Some W_82724.
Proof. vm_refl. Qed.
Lemma D_82724 : decode_any W_82724 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82728 : bv 32 := 0x03413823.
Lemma F_82728 : fetch_word Ubsan.M.loaded_segments (0x82780 : word) = Some W_82728.
Proof. vm_refl. Qed.
Lemma D_82728 : decode_any W_82728 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8272c : bv 32 := 0x03513423.
Lemma F_8272c : fetch_word Ubsan.M.loaded_segments (0x82784 : word) = Some W_8272c.
Proof. vm_refl. Qed.
Lemma D_8272c : decode_any W_8272c = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82730 : bv 32 := 0x04050663.
Lemma F_82730 : fetch_word Ubsan.M.loaded_segments (0x82788 : word) = Some W_82730.
Proof. vm_refl. Qed.
Lemma D_82730 : decode_any W_82730 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82734 : bv 32 := 0x00060413.
Lemma F_82734 : fetch_word Ubsan.M.loaded_segments (0x8278c : word) = Some W_82734.
Proof. vm_refl. Qed.
Lemma D_82734 : decode_any W_82734 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82738 : bv 32 := 0x00058913.
Lemma F_82738 : fetch_word Ubsan.M.loaded_segments (0x82790 : word) = Some W_82738.
Proof. vm_refl. Qed.
Lemma D_82738 : decode_any W_82738 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8273c : bv 32 := 0x00050993.
Lemma F_8273c : fetch_word Ubsan.M.loaded_segments (0x82794 : word) = Some W_8273c.
Proof. vm_refl. Qed.
Lemma D_8273c : decode_any W_8273c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82740 : bv 32 := 0xe9de10ef.
Lemma F_82740 : fetch_word Ubsan.M.loaded_segments (0x82798 : word) = Some W_82740.
Proof. vm_refl. Qed.
Lemma D_82740 : decode_any W_82740 = Some (Jal 1 1973916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82744 : bv 32 := 0x00100593.
Lemma F_82744 : fetch_word Ubsan.M.loaded_segments (0x8279c : word) = Some W_82744.
Proof. vm_refl. Qed.
Lemma D_82744 : decode_any W_82744 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82748 : bv 32 := 0x02b51a63.
Lemma F_82748 : fetch_word Ubsan.M.loaded_segments (0x827a0 : word) = Some W_82748.
Proof. vm_refl. Qed.
Lemma D_82748 : decode_any W_82748 = Some (Branch BC_NE 10 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8274c : bv 32 := 0x00400513.
Lemma F_8274c : fetch_word Ubsan.M.loaded_segments (0x827a4 : word) = Some W_8274c.
Proof. vm_refl. Qed.
Lemma D_8274c : decode_any W_8274c = Some (OpImm ALU_ADD 10 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82750 : bv 32 := 0x0aa96263.
Lemma F_82750 : fetch_word Ubsan.M.loaded_segments (0x827a8 : word) = Some W_82750.
Proof. vm_refl. Qed.
Lemma D_82750 : decode_any W_82750 = Some (Branch BC_LTU 18 10 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827cc : bv 32 := 0x00048513.
Lemma F_827cc : fetch_word Ubsan.M.loaded_segments (0x82824 : word) = Some W_827cc.
Proof. vm_refl. Qed.
Lemma D_827cc : decode_any W_827cc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827d0 : bv 32 := 0x05813083.
Lemma F_827d0 : fetch_word Ubsan.M.loaded_segments (0x82828 : word) = Some W_827d0.
Proof. vm_refl. Qed.
Lemma D_827d0 : decode_any W_827d0 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827d4 : bv 32 := 0x05013403.
Lemma F_827d4 : fetch_word Ubsan.M.loaded_segments (0x8282c : word) = Some W_827d4.
Proof. vm_refl. Qed.
Lemma D_827d4 : decode_any W_827d4 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827d8 : bv 32 := 0x04813483.
Lemma F_827d8 : fetch_word Ubsan.M.loaded_segments (0x82830 : word) = Some W_827d8.
Proof. vm_refl. Qed.
Lemma D_827d8 : decode_any W_827d8 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827dc : bv 32 := 0x04013903.
Lemma F_827dc : fetch_word Ubsan.M.loaded_segments (0x82834 : word) = Some W_827dc.
Proof. vm_refl. Qed.
Lemma D_827dc : decode_any W_827dc = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827e0 : bv 32 := 0x03813983.
Lemma F_827e0 : fetch_word Ubsan.M.loaded_segments (0x82838 : word) = Some W_827e0.
Proof. vm_refl. Qed.
Lemma D_827e0 : decode_any W_827e0 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827e4 : bv 32 := 0x03013a03.
Lemma F_827e4 : fetch_word Ubsan.M.loaded_segments (0x8283c : word) = Some W_827e4.
Proof. vm_refl. Qed.
Lemma D_827e4 : decode_any W_827e4 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827e8 : bv 32 := 0x02813a83.
Lemma F_827e8 : fetch_word Ubsan.M.loaded_segments (0x82840 : word) = Some W_827e8.
Proof. vm_refl. Qed.
Lemma D_827e8 : decode_any W_827e8 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827ec : bv 32 := 0x06010113.
Lemma F_827ec : fetch_word Ubsan.M.loaded_segments (0x82844 : word) = Some W_827ec.
Proof. vm_refl. Qed.
Lemma D_827ec : decode_any W_827ec = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827f0 : bv 32 := 0x00008067.
Lemma F_827f0 : fetch_word Ubsan.M.loaded_segments (0x82848 : word) = Some W_827f0.
Proof. vm_refl. Qed.
Lemma D_827f0 : decode_any W_827f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827f4 : bv 32 := 0x02410593.
Lemma F_827f4 : fetch_word Ubsan.M.loaded_segments (0x8284c : word) = Some W_827f4.
Proof. vm_refl. Qed.
Lemma D_827f4 : decode_any W_827f4 = Some (OpImm ALU_ADD 11 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827f8 : bv 32 := 0x02010613.
Lemma F_827f8 : fetch_word Ubsan.M.loaded_segments (0x82850 : word) = Some W_827f8.
Proof. vm_refl. Qed.
Lemma D_827f8 : decode_any W_827f8 = Some (OpImm ALU_ADD 12 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827fc : bv 32 := 0x02010493.
Lemma F_827fc : fetch_word Ubsan.M.loaded_segments (0x82854 : word) = Some W_827fc.
Proof. vm_refl. Qed.
Lemma D_827fc : decode_any W_827fc = Some (OpImm ALU_ADD 9 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82800 : bv 32 := 0x00098513.
Lemma F_82800 : fetch_word Ubsan.M.loaded_segments (0x82858 : word) = Some W_82800.
Proof. vm_refl. Qed.
Lemma D_82800 : decode_any W_82800 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82804 : bv 32 := 0x00000693.
Lemma F_82804 : fetch_word Ubsan.M.loaded_segments (0x8285c : word) = Some W_82804.
Proof. vm_refl. Qed.
Lemma D_82804 : decode_any W_82804 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82808 : bv 32 := 0x974e10ef.
Lemma F_82808 : fetch_word Ubsan.M.loaded_segments (0x82860 : word) = Some W_82808.
Proof. vm_refl. Qed.
Lemma D_82808 : decode_any W_82808 = Some (Jal 1 1970548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8280c : bv 32 := 0x00200a13.
Lemma F_8280c : fetch_word Ubsan.M.loaded_segments (0x82864 : word) = Some W_8280c.
Proof. vm_refl. Qed.
Lemma D_8280c : decode_any W_8280c = Some (OpImm ALU_ADD 20 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82810 : bv 32 := 0x01496463.
Lemma F_82810 : fetch_word Ubsan.M.loaded_segments (0x82868 : word) = Some W_82810.
Proof. vm_refl. Qed.
Lemma D_82810 : decode_any W_82810 = Some (Branch BC_LTU 18 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82818 : bv 32 := 0x0004a503.
Lemma F_82818 : fetch_word Ubsan.M.loaded_segments (0x82870 : word) = Some W_82818.
Proof. vm_refl. Qed.
Lemma D_82818 : decode_any W_82818 = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8281c : bv 32 := 0xe15de0ef.
Lemma F_8281c : fetch_word Ubsan.M.loaded_segments (0x82874 : word) = Some W_8281c.
Proof. vm_refl. Qed.
Lemma D_8281c : decode_any W_8281c = Some (Jal 1 1961492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82820 : bv 32 := 0x00050493.
Lemma F_82820 : fetch_word Ubsan.M.loaded_segments (0x82878 : word) = Some W_82820.
Proof. vm_refl. Qed.
Lemma D_82820 : decode_any W_82820 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82824 : bv 32 := 0x13490063.
Lemma F_82824 : fetch_word Ubsan.M.loaded_segments (0x8287c : word) = Some W_82824.
Proof. vm_refl. Qed.
Lemma D_82824 : decode_any W_82824 = Some (Branch BC_EQ 18 20 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82828 : bv 32 := 0x00100513.
Lemma F_82828 : fetch_word Ubsan.M.loaded_segments (0x82880 : word) = Some W_82828.
Proof. vm_refl. Qed.
Lemma D_82828 : decode_any W_82828 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8282c : bv 32 := 0x02a90e63.
Lemma F_8282c : fetch_word Ubsan.M.loaded_segments (0x82884 : word) = Some W_8282c.
Proof. vm_refl. Qed.
Lemma D_8282c : decode_any W_8282c = Some (Branch BC_EQ 18 10 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82868 : bv 32 := 0x02412503.
Lemma F_82868 : fetch_word Ubsan.M.loaded_segments (0x828c0 : word) = Some W_82868.
Proof. vm_refl. Qed.
Lemma D_82868 : decode_any W_82868 = Some (Load SZ4 true 10 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8286c : bv 32 := 0xfff5059b.
Lemma F_8286c : fetch_word Ubsan.M.loaded_segments (0x828c4 : word) = Some W_8286c.
Proof. vm_refl. Qed.
Lemma D_8286c : decode_any W_8286c = Some (OpImm32 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82870 : bv 32 := 0x44a5d263.
Lemma F_82870 : fetch_word Ubsan.M.loaded_segments (0x828c8 : word) = Some W_82870.
Proof. vm_refl. Qed.
Lemma D_82870 : decode_any W_82870 = Some (Branch BC_GE 11 10 1092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82874 : bv 32 := 0x00100693.
Lemma F_82874 : fetch_word Ubsan.M.loaded_segments (0x828cc : word) = Some W_82874.
Proof. vm_refl. Qed.
Lemma D_82874 : decode_any W_82874 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82878 : bv 32 := 0x01c10713.
Lemma F_82878 : fetch_word Ubsan.M.loaded_segments (0x828d0 : word) = Some W_82878.
Proof. vm_refl. Qed.
Lemma D_82878 : decode_any W_82878 = Some (OpImm ALU_ADD 14 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8287c : bv 32 := 0x00098513.
Lemma F_8287c : fetch_word Ubsan.M.loaded_segments (0x828d4 : word) = Some W_8287c.
Proof. vm_refl. Qed.
Lemma D_8287c : decode_any W_8287c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82880 : bv 32 := 0x00000613.
Lemma F_82880 : fetch_word Ubsan.M.loaded_segments (0x828d8 : word) = Some W_82880.
Proof. vm_refl. Qed.
Lemma D_82880 : decode_any W_82880 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82884 : bv 32 := 0x434000ef.
Lemma F_82884 : fetch_word Ubsan.M.loaded_segments (0x828dc : word) = Some W_82884.
Proof. vm_refl. Qed.
Lemma D_82884 : decode_any W_82884 = Some (Jal 1 1076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82888 : bv 32 := 0x01c12583.
Lemma F_82888 : fetch_word Ubsan.M.loaded_segments (0x828e0 : word) = Some W_82888.
Proof. vm_refl. Qed.
Lemma D_82888 : decode_any W_82888 = Some (Load SZ4 true 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8288c : bv 32 := 0x00059463.
Lemma F_8288c : fetch_word Ubsan.M.loaded_segments (0x828e4 : word) = Some W_8288c.
Proof. vm_refl. Qed.
Lemma D_8288c : decode_any W_8288c = Some (Branch BC_NE 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82890 : bv 32 := 0x02412583.
Lemma F_82890 : fetch_word Ubsan.M.loaded_segments (0x828e8 : word) = Some W_82890.
Proof. vm_refl. Qed.
Lemma D_82890 : decode_any W_82890 = Some (Load SZ4 true 11 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82894 : bv 32 := 0xfff5851b.
Lemma F_82894 : fetch_word Ubsan.M.loaded_segments (0x828ec : word) = Some W_82894.
Proof. vm_refl. Qed.
Lemma D_82894 : decode_any W_82894 = Some (OpImm32 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82898 : bv 32 := 0x40b55e63.
Lemma F_82898 : fetch_word Ubsan.M.loaded_segments (0x828f0 : word) = Some W_82898.
Proof. vm_refl. Qed.
Lemma D_82898 : decode_any W_82898 = Some (Branch BC_GE 10 11 1052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8289c : bv 32 := 0x00a12e23.
Lemma F_8289c : fetch_word Ubsan.M.loaded_segments (0x828f4 : word) = Some W_8289c.
Proof. vm_refl. Qed.
Lemma D_8289c : decode_any W_8289c = Some (Store SZ4 2 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828a0 : bv 32 := 0xd0057553.
Lemma F_828a0 : fetch_word Ubsan.M.loaded_segments (0x828f8 : word) = Some W_828a0.
Proof. vm_refl. Qed.
Lemma D_828a0 : decode_any W_828a0 = Some (Fcvt FC_S FC_W 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828a4 : bv 32 := 0x00048513.
Lemma F_828a4 : fetch_word Ubsan.M.loaded_segments (0x828fc : word) = Some W_828a4.
Proof. vm_refl. Qed.
Lemma D_828a4 : decode_any W_828a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828a8 : bv 32 := 0xf49de0ef.
Lemma F_828a8 : fetch_word Ubsan.M.loaded_segments (0x82900 : word) = Some W_828a8.
Proof. vm_refl. Qed.
Lemma D_828a8 : decode_any W_828a8 = Some (Jal 1 1961800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828ac : bv 32 := 0x02012503.
Lemma F_828ac : fetch_word Ubsan.M.loaded_segments (0x82904 : word) = Some W_828ac.
Proof. vm_refl. Qed.
Lemma D_828ac : decode_any W_828ac = Some (Load SZ4 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828b0 : bv 32 := 0x00200593.
Lemma F_828b0 : fetch_word Ubsan.M.loaded_segments (0x82908 : word) = Some W_828b0.
Proof. vm_refl. Qed.
Lemma D_828b0 : decode_any W_828b0 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828b4 : bv 32 := 0x32b54063.
Lemma F_828b4 : fetch_word Ubsan.M.loaded_segments (0x8290c : word) = Some W_828b4.
Proof. vm_refl. Qed.
Lemma D_828b4 : decode_any W_828b4 = Some (Branch BC_LT 10 11 800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828b8 : bv 32 := 0x00100a93.
Lemma F_828b8 : fetch_word Ubsan.M.loaded_segments (0x82910 : word) = Some W_828b8.
Proof. vm_refl. Qed.
Lemma D_828b8 : decode_any W_828b8 = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828bc : bv 32 := 0x00100a13.
Lemma F_828bc : fetch_word Ubsan.M.loaded_segments (0x82914 : word) = Some W_828bc.
Proof. vm_refl. Qed.
Lemma D_828bc : decode_any W_828bc = Some (OpImm ALU_ADD 20 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828c0 : bv 32 := 0x0340006f.
Lemma F_828c0 : fetch_word Ubsan.M.loaded_segments (0x82918 : word) = Some W_828c0.
Proof. vm_refl. Qed.
Lemma D_828c0 : decode_any W_828c0 = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828c4 : bv 32 := 0x01c10713.
Lemma F_828c4 : fetch_word Ubsan.M.loaded_segments (0x8291c : word) = Some W_828c4.
Proof. vm_refl. Qed.
Lemma D_828c4 : decode_any W_828c4 = Some (OpImm ALU_ADD 14 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828c8 : bv 32 := 0x00098513.
Lemma F_828c8 : fetch_word Ubsan.M.loaded_segments (0x82920 : word) = Some W_828c8.
Proof. vm_refl. Qed.
Lemma D_828c8 : decode_any W_828c8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828cc : bv 32 := 0x000a0613.
Lemma F_828cc : fetch_word Ubsan.M.loaded_segments (0x82924 : word) = Some W_828cc.
Proof. vm_refl. Qed.
Lemma D_828cc : decode_any W_828cc = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828d0 : bv 32 := 0x00000693.
Lemma F_828d0 : fetch_word Ubsan.M.loaded_segments (0x82928 : word) = Some W_828d0.
Proof. vm_refl. Qed.
Lemma D_828d0 : decode_any W_828d0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828d4 : bv 32 := 0x648000ef.
Lemma F_828d4 : fetch_word Ubsan.M.loaded_segments (0x8292c : word) = Some W_828d4.
Proof. vm_refl. Qed.
Lemma D_828d4 : decode_any W_828d4 = Some (Jal 1 1608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828d8 : bv 32 := 0x01c12503.
Lemma F_828d8 : fetch_word Ubsan.M.loaded_segments (0x82930 : word) = Some W_828d8.
Proof. vm_refl. Qed.
Lemma D_828d8 : decode_any W_828d8 = Some (Load SZ4 true 10 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828dc : bv 32 := 0xd0057553.
Lemma F_828dc : fetch_word Ubsan.M.loaded_segments (0x82934 : word) = Some W_828dc.
Proof. vm_refl. Qed.
Lemma D_828dc : decode_any W_828dc = Some (Fcvt FC_S FC_W 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828e0 : bv 32 := 0x00048513.
Lemma F_828e0 : fetch_word Ubsan.M.loaded_segments (0x82938 : word) = Some W_828e0.
Proof. vm_refl. Qed.
Lemma D_828e0 : decode_any W_828e0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828e4 : bv 32 := 0xf0dde0ef.
Lemma F_828e4 : fetch_word Ubsan.M.loaded_segments (0x8293c : word) = Some W_828e4.
Proof. vm_refl. Qed.
Lemma D_828e4 : decode_any W_828e4 = Some (Jal 1 1961740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828e8 : bv 32 := 0x02012503.
Lemma F_828e8 : fetch_word Ubsan.M.loaded_segments (0x82940 : word) = Some W_828e8.
Proof. vm_refl. Qed.
Lemma D_828e8 : decode_any W_828e8 = Some (Load SZ4 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828ec : bv 32 := 0x001a0a1b.
Lemma F_828ec : fetch_word Ubsan.M.loaded_segments (0x82944 : word) = Some W_828ec.
Proof. vm_refl. Qed.
Lemma D_828ec : decode_any W_828ec = Some (OpImm32 20 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828f0 : bv 32 := 0x2eaa5263.
Lemma F_828f0 : fetch_word Ubsan.M.loaded_segments (0x82948 : word) = Some W_828f0.
Proof. vm_refl. Qed.
Lemma D_828f0 : decode_any W_828f0 = Some (Branch BC_GE 20 10 740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828f4 : bv 32 := 0x01c12583.
Lemma F_828f4 : fetch_word Ubsan.M.loaded_segments (0x8294c : word) = Some W_828f4.
Proof. vm_refl. Qed.
Lemma D_828f4 : decode_any W_828f4 = Some (Load SZ4 true 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828f8 : bv 32 := 0x01410693.
Lemma F_828f8 : fetch_word Ubsan.M.loaded_segments (0x82950 : word) = Some W_828f8.
Proof. vm_refl. Qed.
Lemma D_828f8 : decode_any W_828f8 = Some (OpImm ALU_ADD 13 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828fc : bv 32 := 0x00098513.
Lemma F_828fc : fetch_word Ubsan.M.loaded_segments (0x82954 : word) = Some W_828fc.
Proof. vm_refl. Qed.
Lemma D_828fc : decode_any W_828fc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82900 : bv 32 := 0x000a0613.
Lemma F_82900 : fetch_word Ubsan.M.loaded_segments (0x82958 : word) = Some W_82900.
Proof. vm_refl. Qed.
Lemma D_82900 : decode_any W_82900 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82904 : bv 32 := 0x810e20ef.
Lemma F_82904 : fetch_word Ubsan.M.loaded_segments (0x8295c : word) = Some W_82904.
Proof. vm_refl. Qed.
Lemma D_82904 : decode_any W_82904 = Some (Jal 1 1974288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82908 : bv 32 := 0x01412503.
Lemma F_82908 : fetch_word Ubsan.M.loaded_segments (0x82960 : word) = Some W_82908.
Proof. vm_refl. Qed.
Lemma D_82908 : decode_any W_82908 = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8290c : bv 32 := 0x01c12583.
Lemma F_8290c : fetch_word Ubsan.M.loaded_segments (0x82964 : word) = Some W_8290c.
Proof. vm_refl. Qed.
Lemma D_8290c : decode_any W_8290c = Some (Load SZ4 true 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82910 : bv 32 := 0xfb550ae3.
Lemma F_82910 : fetch_word Ubsan.M.loaded_segments (0x82968 : word) = Some W_82910.
Proof. vm_refl. Qed.
Lemma D_82910 : decode_any W_82910 = Some (Branch BC_EQ 10 21 8116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82914 : bv 32 := 0x00100693.
Lemma F_82914 : fetch_word Ubsan.M.loaded_segments (0x8296c : word) = Some W_82914.
Proof. vm_refl. Qed.
Lemma D_82914 : decode_any W_82914 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82918 : bv 32 := 0x01c10713.
Lemma F_82918 : fetch_word Ubsan.M.loaded_segments (0x82970 : word) = Some W_82918.
Proof. vm_refl. Qed.
Lemma D_82918 : decode_any W_82918 = Some (OpImm ALU_ADD 14 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8291c : bv 32 := 0x00098513.
Lemma F_8291c : fetch_word Ubsan.M.loaded_segments (0x82974 : word) = Some W_8291c.
Proof. vm_refl. Qed.
Lemma D_8291c : decode_any W_8291c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82920 : bv 32 := 0x000a0613.
Lemma F_82920 : fetch_word Ubsan.M.loaded_segments (0x82978 : word) = Some W_82920.
Proof. vm_refl. Qed.
Lemma D_82920 : decode_any W_82920 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82924 : bv 32 := 0x394000ef.
Lemma F_82924 : fetch_word Ubsan.M.loaded_segments (0x8297c : word) = Some W_82924.
Proof. vm_refl. Qed.
Lemma D_82924 : decode_any W_82924 = Some (Jal 1 916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82928 : bv 32 := 0x01c12583.
Lemma F_82928 : fetch_word Ubsan.M.loaded_segments (0x82980 : word) = Some W_82928.
Proof. vm_refl. Qed.
Lemma D_82928 : decode_any W_82928 = Some (Load SZ4 true 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8292c : bv 32 := 0x00059463.
Lemma F_8292c : fetch_word Ubsan.M.loaded_segments (0x82984 : word) = Some W_8292c.
Proof. vm_refl. Qed.
Lemma D_8292c : decode_any W_8292c = Some (Branch BC_NE 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82930 : bv 32 := 0x02412583.
Lemma F_82930 : fetch_word Ubsan.M.loaded_segments (0x82988 : word) = Some W_82930.
Proof. vm_refl. Qed.
Lemma D_82930 : decode_any W_82930 = Some (Load SZ4 true 11 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82934 : bv 32 := 0xfff5851b.
Lemma F_82934 : fetch_word Ubsan.M.loaded_segments (0x8298c : word) = Some W_82934.
Proof. vm_refl. Qed.
Lemma D_82934 : decode_any W_82934 = Some (OpImm32 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82938 : bv 32 := 0x36b55e63.
Lemma F_82938 : fetch_word Ubsan.M.loaded_segments (0x82990 : word) = Some W_82938.
Proof. vm_refl. Qed.
Lemma D_82938 : decode_any W_82938 = Some (Branch BC_GE 10 11 892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8293c : bv 32 := 0x00a12e23.
Lemma F_8293c : fetch_word Ubsan.M.loaded_segments (0x82994 : word) = Some W_8293c.
Proof. vm_refl. Qed.
Lemma D_8293c : decode_any W_8293c = Some (Store SZ4 2 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82940 : bv 32 := 0xf9dff06f.
Lemma F_82940 : fetch_word Ubsan.M.loaded_segments (0x82998 : word) = Some W_82940.
Proof. vm_refl. Qed.
Lemma D_82940 : decode_any W_82940 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82bd4 : bv 32 := 0xbe040ce3.
Lemma F_82bd4 : fetch_word Ubsan.M.loaded_segments (0x82c2c : word) = Some W_82bd4.
Proof. vm_refl. Qed.
Lemma D_82bd4 : decode_any W_82bd4 = Some (Branch BC_EQ 8 0 7160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cb8 : bv 32 := 0xfb010113.
Lemma F_82cb8 : fetch_word Ubsan.M.loaded_segments (0x82d10 : word) = Some W_82cb8.
Proof. vm_refl. Qed.
Lemma D_82cb8 : decode_any W_82cb8 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cbc : bv 32 := 0x04113423.
Lemma F_82cbc : fetch_word Ubsan.M.loaded_segments (0x82d14 : word) = Some W_82cbc.
Proof. vm_refl. Qed.
Lemma D_82cbc : decode_any W_82cbc = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cc0 : bv 32 := 0x04813023.
Lemma F_82cc0 : fetch_word Ubsan.M.loaded_segments (0x82d18 : word) = Some W_82cc0.
Proof. vm_refl. Qed.
Lemma D_82cc0 : decode_any W_82cc0 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cc4 : bv 32 := 0x02913c23.
Lemma F_82cc4 : fetch_word Ubsan.M.loaded_segments (0x82d1c : word) = Some W_82cc4.
Proof. vm_refl. Qed.
Lemma D_82cc4 : decode_any W_82cc4 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cc8 : bv 32 := 0x03213823.
Lemma F_82cc8 : fetch_word Ubsan.M.loaded_segments (0x82d20 : word) = Some W_82cc8.
Proof. vm_refl. Qed.
Lemma D_82cc8 : decode_any W_82cc8 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ccc : bv 32 := 0x03313423.
Lemma F_82ccc : fetch_word Ubsan.M.loaded_segments (0x82d24 : word) = Some W_82ccc.
Proof. vm_refl. Qed.
Lemma D_82ccc : decode_any W_82ccc = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cd0 : bv 32 := 0x03413023.
Lemma F_82cd0 : fetch_word Ubsan.M.loaded_segments (0x82d28 : word) = Some W_82cd0.
Proof. vm_refl. Qed.
Lemma D_82cd0 : decode_any W_82cd0 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cd4 : bv 32 := 0x01513c23.
Lemma F_82cd4 : fetch_word Ubsan.M.loaded_segments (0x82d2c : word) = Some W_82cd4.
Proof. vm_refl. Qed.
Lemma D_82cd4 : decode_any W_82cd4 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cd8 : bv 32 := 0x08070863.
Lemma F_82cd8 : fetch_word Ubsan.M.loaded_segments (0x82d30 : word) = Some W_82cd8.
Proof. vm_refl. Qed.
Lemma D_82cd8 : decode_any W_82cd8 = Some (Branch BC_EQ 14 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cdc : bv 32 := 0x00070413.
Lemma F_82cdc : fetch_word Ubsan.M.loaded_segments (0x82d34 : word) = Some W_82cdc.
Proof. vm_refl. Qed.
Lemma D_82cdc : decode_any W_82cdc = Some (OpImm ALU_ADD 8 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ce0 : bv 32 := 0x00050993.
Lemma F_82ce0 : fetch_word Ubsan.M.loaded_segments (0x82d38 : word) = Some W_82ce0.
Proof. vm_refl. Qed.
Lemma D_82ce0 : decode_any W_82ce0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ce4 : bv 32 := 0x00377513.
Lemma F_82ce4 : fetch_word Ubsan.M.loaded_segments (0x82d3c : word) = Some W_82ce4.
Proof. vm_refl. Qed.
Lemma D_82ce4 : decode_any W_82ce4 = Some (OpImm ALU_AND 10 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ce8 : bv 32 := 0x22051863.
Lemma F_82ce8 : fetch_word Ubsan.M.loaded_segments (0x82d40 : word) = Some W_82ce8.
Proof. vm_refl. Qed.
Lemma D_82ce8 : decode_any W_82ce8 = Some (Branch BC_NE 10 0 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cec : bv 32 := 0x00042023.
Lemma F_82cec : fetch_word Ubsan.M.loaded_segments (0x82d44 : word) = Some W_82cec.
Proof. vm_refl. Qed.
Lemma D_82cec : decode_any W_82cec = Some (Store SZ4 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cf0 : bv 32 := 0x04098863.
Lemma F_82cf0 : fetch_word Ubsan.M.loaded_segments (0x82d48 : word) = Some W_82cf0.
Proof. vm_refl. Qed.
Lemma D_82cf0 : decode_any W_82cf0 = Some (Branch BC_EQ 19 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cf4 : bv 32 := 0x00068a13.
Lemma F_82cf4 : fetch_word Ubsan.M.loaded_segments (0x82d4c : word) = Some W_82cf4.
Proof. vm_refl. Qed.
Lemma D_82cf4 : decode_any W_82cf4 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cf8 : bv 32 := 0x00060493.
Lemma F_82cf8 : fetch_word Ubsan.M.loaded_segments (0x82d50 : word) = Some W_82cf8.
Proof. vm_refl. Qed.
Lemma D_82cf8 : decode_any W_82cf8 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82cfc : bv 32 := 0x00058913.
Lemma F_82cfc : fetch_word Ubsan.M.loaded_segments (0x82d54 : word) = Some W_82cfc.
Proof. vm_refl. Qed.
Lemma D_82cfc : decode_any W_82cfc = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82d00 : bv 32 := 0x00098513.
Lemma F_82d00 : fetch_word Ubsan.M.loaded_segments (0x82d58 : word) = Some W_82d00.
Proof. vm_refl. Qed.
Lemma D_82d00 : decode_any W_82d00 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82d04 : bv 32 := 0x8d9e10ef.
Lemma F_82d04 : fetch_word Ubsan.M.loaded_segments (0x82d5c : word) = Some W_82d04.
Proof. vm_refl. Qed.
Lemma D_82d04 : decode_any W_82d04 = Some (Jal 1 1972440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82d08 : bv 32 := 0x00100593.
Lemma F_82d08 : fetch_word Ubsan.M.loaded_segments (0x82d60 : word) = Some W_82d08.
Proof. vm_refl. Qed.
Lemma D_82d08 : decode_any W_82d08 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82d0c : bv 32 := 0x02b51a63.
Lemma F_82d0c : fetch_word Ubsan.M.loaded_segments (0x82d64 : word) = Some W_82d0c.
Proof. vm_refl. Qed.
Lemma D_82d0c : decode_any W_82d0c = Some (Branch BC_NE 10 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82d10 : bv 32 := 0x00400513.
Lemma F_82d10 : fetch_word Ubsan.M.loaded_segments (0x82d68 : word) = Some W_82d10.
Proof. vm_refl. Qed.
Lemma D_82d10 : decode_any W_82d10 = Some (OpImm ALU_ADD 10 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82d14 : bv 32 := 0x0caa6463.
Lemma F_82d14 : fetch_word Ubsan.M.loaded_segments (0x82d6c : word) = Some W_82d14.
Proof. vm_refl. Qed.
Lemma D_82d14 : decode_any W_82d14 = Some (Branch BC_LTU 20 10 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82db8 : bv 32 := 0x04813083.
Lemma F_82db8 : fetch_word Ubsan.M.loaded_segments (0x82e10 : word) = Some W_82db8.
Proof. vm_refl. Qed.
Lemma D_82db8 : decode_any W_82db8 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dbc : bv 32 := 0x04013403.
Lemma F_82dbc : fetch_word Ubsan.M.loaded_segments (0x82e14 : word) = Some W_82dbc.
Proof. vm_refl. Qed.
Lemma D_82dbc : decode_any W_82dbc = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dc0 : bv 32 := 0x03813483.
Lemma F_82dc0 : fetch_word Ubsan.M.loaded_segments (0x82e18 : word) = Some W_82dc0.
Proof. vm_refl. Qed.
Lemma D_82dc0 : decode_any W_82dc0 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dc4 : bv 32 := 0x03013903.
Lemma F_82dc4 : fetch_word Ubsan.M.loaded_segments (0x82e1c : word) = Some W_82dc4.
Proof. vm_refl. Qed.
Lemma D_82dc4 : decode_any W_82dc4 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dc8 : bv 32 := 0x02813983.
Lemma F_82dc8 : fetch_word Ubsan.M.loaded_segments (0x82e20 : word) = Some W_82dc8.
Proof. vm_refl. Qed.
Lemma D_82dc8 : decode_any W_82dc8 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dcc : bv 32 := 0x02013a03.
Lemma F_82dcc : fetch_word Ubsan.M.loaded_segments (0x82e24 : word) = Some W_82dcc.
Proof. vm_refl. Qed.
Lemma D_82dcc : decode_any W_82dcc = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dd0 : bv 32 := 0x01813a83.
Lemma F_82dd0 : fetch_word Ubsan.M.loaded_segments (0x82e28 : word) = Some W_82dd0.
Proof. vm_refl. Qed.
Lemma D_82dd0 : decode_any W_82dd0 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dd4 : bv 32 := 0x05010113.
Lemma F_82dd4 : fetch_word Ubsan.M.loaded_segments (0x82e2c : word) = Some W_82dd4.
Proof. vm_refl. Qed.
Lemma D_82dd4 : decode_any W_82dd4 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dd8 : bv 32 := 0x00008067.
Lemma F_82dd8 : fetch_word Ubsan.M.loaded_segments (0x82e30 : word) = Some W_82dd8.
Proof. vm_refl. Qed.
Lemma D_82dd8 : decode_any W_82dd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ddc : bv 32 := 0x01410593.
Lemma F_82ddc : fetch_word Ubsan.M.loaded_segments (0x82e34 : word) = Some W_82ddc.
Proof. vm_refl. Qed.
Lemma D_82ddc : decode_any W_82ddc = Some (OpImm ALU_ADD 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82de0 : bv 32 := 0x01010613.
Lemma F_82de0 : fetch_word Ubsan.M.loaded_segments (0x82e38 : word) = Some W_82de0.
Proof. vm_refl. Qed.
Lemma D_82de0 : decode_any W_82de0 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82de4 : bv 32 := 0x00098513.
Lemma F_82de4 : fetch_word Ubsan.M.loaded_segments (0x82e3c : word) = Some W_82de4.
Proof. vm_refl. Qed.
Lemma D_82de4 : decode_any W_82de4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82de8 : bv 32 := 0x00000693.
Lemma F_82de8 : fetch_word Ubsan.M.loaded_segments (0x82e40 : word) = Some W_82de8.
Proof. vm_refl. Qed.
Lemma D_82de8 : decode_any W_82de8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dec : bv 32 := 0xb91e00ef.
Lemma F_82dec : fetch_word Ubsan.M.loaded_segments (0x82e44 : word) = Some W_82dec.
Proof. vm_refl. Qed.
Lemma D_82dec : decode_any W_82dec = Some (Jal 1 1969040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82df0 : bv 32 := 0x00100513.
Lemma F_82df0 : fetch_word Ubsan.M.loaded_segments (0x82e48 : word) = Some W_82df0.
Proof. vm_refl. Qed.
Lemma D_82df0 : decode_any W_82df0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82df4 : bv 32 := 0x05454863.
Lemma F_82df4 : fetch_word Ubsan.M.loaded_segments (0x82e4c : word) = Some W_82df4.
Proof. vm_refl. Qed.
Lemma D_82df4 : decode_any W_82df4 = Some (Branch BC_LT 10 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82df8 : bv 32 := 0x080a1a63.
Lemma F_82df8 : fetch_word Ubsan.M.loaded_segments (0x82e50 : word) = Some W_82df8.
Proof. vm_refl. Qed.
Lemma D_82df8 : decode_any W_82df8 = Some (Branch BC_NE 20 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e38 : bv 32 := 0x00000513.
Lemma F_82e38 : fetch_word Ubsan.M.loaded_segments (0x82e90 : word) = Some W_82e38.
Proof. vm_refl. Qed.
Lemma D_82e38 : decode_any W_82e38 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e3c : bv 32 := 0x00b42023.
Lemma F_82e3c : fetch_word Ubsan.M.loaded_segments (0x82e94 : word) = Some W_82e3c.
Proof. vm_refl. Qed.
Lemma D_82e3c : decode_any W_82e3c = Some (Store SZ4 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e40 : bv 32 := 0xf79ff06f.
Lemma F_82e40 : fetch_word Ubsan.M.loaded_segments (0x82e98 : word) = Some W_82e40.
Proof. vm_refl. Qed.
Lemma D_82e40 : decode_any W_82e40 = Some (Jal 0 2097016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e8c : bv 32 := 0x06094a63.
Lemma F_82e8c : fetch_word Ubsan.M.loaded_segments (0x82ee4 : word) = Some W_82e8c.
Proof. vm_refl. Qed.
Lemma D_82e8c : decode_any W_82e8c = Some (Branch BC_LT 18 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e90 : bv 32 := 0x00100a93.
Lemma F_82e90 : fetch_word Ubsan.M.loaded_segments (0x82ee8 : word) = Some W_82e90.
Proof. vm_refl. Qed.
Lemma D_82e90 : decode_any W_82e90 = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e94 : bv 32 := 0x00090a13.
Lemma F_82e94 : fetch_word Ubsan.M.loaded_segments (0x82eec : word) = Some W_82e94.
Proof. vm_refl. Qed.
Lemma D_82e94 : decode_any W_82e94 = Some (OpImm ALU_ADD 20 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e98 : bv 32 := 0x00c10693.
Lemma F_82e98 : fetch_word Ubsan.M.loaded_segments (0x82ef0 : word) = Some W_82e98.
Proof. vm_refl. Qed.
Lemma D_82e98 : decode_any W_82e98 = Some (OpImm ALU_ADD 13 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e9c : bv 32 := 0x00098513.
Lemma F_82e9c : fetch_word Ubsan.M.loaded_segments (0x82ef4 : word) = Some W_82e9c.
Proof. vm_refl. Qed.
Lemma D_82e9c : decode_any W_82e9c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ea0 : bv 32 := 0x00090593.
Lemma F_82ea0 : fetch_word Ubsan.M.loaded_segments (0x82ef8 : word) = Some W_82ea0.
Proof. vm_refl. Qed.
Lemma D_82ea0 : decode_any W_82ea0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ea4 : bv 32 := 0x00048613.
Lemma F_82ea4 : fetch_word Ubsan.M.loaded_segments (0x82efc : word) = Some W_82ea4.
Proof. vm_refl. Qed.
Lemma D_82ea4 : decode_any W_82ea4 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ea8 : bv 32 := 0xa6de10ef.
Lemma F_82ea8 : fetch_word Ubsan.M.loaded_segments (0x82f00 : word) = Some W_82ea8.
Proof. vm_refl. Qed.
Lemma D_82ea8 : decode_any W_82ea8 = Some (Jal 1 1972844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82eac : bv 32 := 0x00c12503.
Lemma F_82eac : fetch_word Ubsan.M.loaded_segments (0x82f04 : word) = Some W_82eac.
Proof. vm_refl. Qed.
Lemma D_82eac : decode_any W_82eac = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82eb0 : bv 32 := 0x05550663.
Lemma F_82eb0 : fetch_word Ubsan.M.loaded_segments (0x82f08 : word) = Some W_82eb0.
Proof. vm_refl. Qed.
Lemma D_82eb0 : decode_any W_82eb0 = Some (Branch BC_EQ 10 21 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82eb4 : bv 32 := 0xfffa091b.
Lemma F_82eb4 : fetch_word Ubsan.M.loaded_segments (0x82f0c : word) = Some W_82eb4.
Proof. vm_refl. Qed.
Lemma D_82eb4 : decode_any W_82eb4 = Some (OpImm32 18 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82eb8 : bv 32 := 0xfd404ee3.
Lemma F_82eb8 : fetch_word Ubsan.M.loaded_segments (0x82f10 : word) = Some W_82eb8.
Proof. vm_refl. Qed.
Lemma D_82eb8 : decode_any W_82eb8 = Some (Branch BC_LT 0 20 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ebc : bv 32 := 0xfff00913.
Lemma F_82ebc : fetch_word Ubsan.M.loaded_segments (0x82f14 : word) = Some W_82ebc.
Proof. vm_refl. Qed.
Lemma D_82ebc : decode_any W_82ebc = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ec0 : bv 32 := 0x0400006f.
Lemma F_82ec0 : fetch_word Ubsan.M.loaded_segments (0x82f18 : word) = Some W_82ec0.
Proof. vm_refl. Qed.
Lemma D_82ec0 : decode_any W_82ec0 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82efc : bv 32 := 0x000a0913.
Lemma F_82efc : fetch_word Ubsan.M.loaded_segments (0x82f54 : word) = Some W_82efc.
Proof. vm_refl. Qed.
Lemma D_82efc : decode_any W_82efc = Some (OpImm ALU_ADD 18 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f00 : bv 32 := 0x0019059b.
Lemma F_82f00 : fetch_word Ubsan.M.loaded_segments (0x82f58 : word) = Some W_82f00.
Proof. vm_refl. Qed.
Lemma D_82f00 : decode_any W_82f00 = Some (OpImm32 11 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f04 : bv 32 := 0xf325dae3.
Lemma F_82f04 : fetch_word Ubsan.M.loaded_segments (0x82f5c : word) = Some W_82f04.
Proof. vm_refl. Qed.
Lemma D_82f04 : decode_any W_82f04 = Some (Branch BC_GE 11 18 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f1c : bv 32 := 0xfc010113.
Lemma F_82f1c : fetch_word Ubsan.M.loaded_segments (0x82f74 : word) = Some W_82f1c.
Proof. vm_refl. Qed.
Lemma D_82f1c : decode_any W_82f1c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f20 : bv 32 := 0x02113c23.
Lemma F_82f20 : fetch_word Ubsan.M.loaded_segments (0x82f78 : word) = Some W_82f20.
Proof. vm_refl. Qed.
Lemma D_82f20 : decode_any W_82f20 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f24 : bv 32 := 0x02813823.
Lemma F_82f24 : fetch_word Ubsan.M.loaded_segments (0x82f7c : word) = Some W_82f24.
Proof. vm_refl. Qed.
Lemma D_82f24 : decode_any W_82f24 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f28 : bv 32 := 0x02913423.
Lemma F_82f28 : fetch_word Ubsan.M.loaded_segments (0x82f80 : word) = Some W_82f28.
Proof. vm_refl. Qed.
Lemma D_82f28 : decode_any W_82f28 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f2c : bv 32 := 0x03213023.
Lemma F_82f2c : fetch_word Ubsan.M.loaded_segments (0x82f84 : word) = Some W_82f2c.
Proof. vm_refl. Qed.
Lemma D_82f2c : decode_any W_82f2c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f30 : bv 32 := 0x01313c23.
Lemma F_82f30 : fetch_word Ubsan.M.loaded_segments (0x82f88 : word) = Some W_82f30.
Proof. vm_refl. Qed.
Lemma D_82f30 : decode_any W_82f30 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f34 : bv 32 := 0x01413823.
Lemma F_82f34 : fetch_word Ubsan.M.loaded_segments (0x82f8c : word) = Some W_82f34.
Proof. vm_refl. Qed.
Lemma D_82f34 : decode_any W_82f34 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f38 : bv 32 := 0x08070863.
Lemma F_82f38 : fetch_word Ubsan.M.loaded_segments (0x82f90 : word) = Some W_82f38.
Proof. vm_refl. Qed.
Lemma D_82f38 : decode_any W_82f38 = Some (Branch BC_EQ 14 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f3c : bv 32 := 0x00070413.
Lemma F_82f3c : fetch_word Ubsan.M.loaded_segments (0x82f94 : word) = Some W_82f3c.
Proof. vm_refl. Qed.
Lemma D_82f3c : decode_any W_82f3c = Some (OpImm ALU_ADD 8 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f40 : bv 32 := 0x00050993.
Lemma F_82f40 : fetch_word Ubsan.M.loaded_segments (0x82f98 : word) = Some W_82f40.
Proof. vm_refl. Qed.
Lemma D_82f40 : decode_any W_82f40 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f44 : bv 32 := 0x00377513.
Lemma F_82f44 : fetch_word Ubsan.M.loaded_segments (0x82f9c : word) = Some W_82f44.
Proof. vm_refl. Qed.
Lemma D_82f44 : decode_any W_82f44 = Some (OpImm ALU_AND 10 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f48 : bv 32 := 0x20051c63.
Lemma F_82f48 : fetch_word Ubsan.M.loaded_segments (0x82fa0 : word) = Some W_82f48.
Proof. vm_refl. Qed.
Lemma D_82f48 : decode_any W_82f48 = Some (Branch BC_NE 10 0 536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f4c : bv 32 := 0x00042023.
Lemma F_82f4c : fetch_word Ubsan.M.loaded_segments (0x82fa4 : word) = Some W_82f4c.
Proof. vm_refl. Qed.
Lemma D_82f4c : decode_any W_82f4c = Some (Store SZ4 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f50 : bv 32 := 0x04098863.
Lemma F_82f50 : fetch_word Ubsan.M.loaded_segments (0x82fa8 : word) = Some W_82f50.
Proof. vm_refl. Qed.
Lemma D_82f50 : decode_any W_82f50 = Some (Branch BC_EQ 19 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f54 : bv 32 := 0x00068a13.
Lemma F_82f54 : fetch_word Ubsan.M.loaded_segments (0x82fac : word) = Some W_82f54.
Proof. vm_refl. Qed.
Lemma D_82f54 : decode_any W_82f54 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f58 : bv 32 := 0x00060493.
Lemma F_82f58 : fetch_word Ubsan.M.loaded_segments (0x82fb0 : word) = Some W_82f58.
Proof. vm_refl. Qed.
Lemma D_82f58 : decode_any W_82f58 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f5c : bv 32 := 0x00058913.
Lemma F_82f5c : fetch_word Ubsan.M.loaded_segments (0x82fb4 : word) = Some W_82f5c.
Proof. vm_refl. Qed.
Lemma D_82f5c : decode_any W_82f5c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f60 : bv 32 := 0x00098513.
Lemma F_82f60 : fetch_word Ubsan.M.loaded_segments (0x82fb8 : word) = Some W_82f60.
Proof. vm_refl. Qed.
Lemma D_82f60 : decode_any W_82f60 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f64 : bv 32 := 0xe78e10ef.
Lemma F_82f64 : fetch_word Ubsan.M.loaded_segments (0x82fbc : word) = Some W_82f64.
Proof. vm_refl. Qed.
Lemma D_82f64 : decode_any W_82f64 = Some (Jal 1 1971832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f68 : bv 32 := 0x00100593.
Lemma F_82f68 : fetch_word Ubsan.M.loaded_segments (0x82fc0 : word) = Some W_82f68.
Proof. vm_refl. Qed.
Lemma D_82f68 : decode_any W_82f68 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f6c : bv 32 := 0x02b51a63.
Lemma F_82f6c : fetch_word Ubsan.M.loaded_segments (0x82fc4 : word) = Some W_82f6c.
Proof. vm_refl. Qed.
Lemma D_82f6c : decode_any W_82f6c = Some (Branch BC_NE 10 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f70 : bv 32 := 0x00400513.
Lemma F_82f70 : fetch_word Ubsan.M.loaded_segments (0x82fc8 : word) = Some W_82f70.
Proof. vm_refl. Qed.
Lemma D_82f70 : decode_any W_82f70 = Some (OpImm ALU_ADD 10 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82f74 : bv 32 := 0x0caa6063.
Lemma F_82f74 : fetch_word Ubsan.M.loaded_segments (0x82fcc : word) = Some W_82f74.
Proof. vm_refl. Qed.
Lemma D_82f74 : decode_any W_82f74 = Some (Branch BC_LTU 20 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83014 : bv 32 := 0x03813083.
Lemma F_83014 : fetch_word Ubsan.M.loaded_segments (0x8306c : word) = Some W_83014.
Proof. vm_refl. Qed.
Lemma D_83014 : decode_any W_83014 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83018 : bv 32 := 0x03013403.
Lemma F_83018 : fetch_word Ubsan.M.loaded_segments (0x83070 : word) = Some W_83018.
Proof. vm_refl. Qed.
Lemma D_83018 : decode_any W_83018 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8301c : bv 32 := 0x02813483.
Lemma F_8301c : fetch_word Ubsan.M.loaded_segments (0x83074 : word) = Some W_8301c.
Proof. vm_refl. Qed.
Lemma D_8301c : decode_any W_8301c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83020 : bv 32 := 0x02013903.
Lemma F_83020 : fetch_word Ubsan.M.loaded_segments (0x83078 : word) = Some W_83020.
Proof. vm_refl. Qed.
Lemma D_83020 : decode_any W_83020 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83024 : bv 32 := 0x01813983.
Lemma F_83024 : fetch_word Ubsan.M.loaded_segments (0x8307c : word) = Some W_83024.
Proof. vm_refl. Qed.
Lemma D_83024 : decode_any W_83024 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83028 : bv 32 := 0x01013a03.
Lemma F_83028 : fetch_word Ubsan.M.loaded_segments (0x83080 : word) = Some W_83028.
Proof. vm_refl. Qed.
Lemma D_83028 : decode_any W_83028 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8302c : bv 32 := 0x04010113.
Lemma F_8302c : fetch_word Ubsan.M.loaded_segments (0x83084 : word) = Some W_8302c.
Proof. vm_refl. Qed.
Lemma D_8302c : decode_any W_8302c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83030 : bv 32 := 0x00008067.
Lemma F_83030 : fetch_word Ubsan.M.loaded_segments (0x83088 : word) = Some W_83030.
Proof. vm_refl. Qed.
Lemma D_83030 : decode_any W_83030 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83034 : bv 32 := 0x00c10593.
Lemma F_83034 : fetch_word Ubsan.M.loaded_segments (0x8308c : word) = Some W_83034.
Proof. vm_refl. Qed.
Lemma D_83034 : decode_any W_83034 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83038 : bv 32 := 0x00810613.
Lemma F_83038 : fetch_word Ubsan.M.loaded_segments (0x83090 : word) = Some W_83038.
Proof. vm_refl. Qed.
Lemma D_83038 : decode_any W_83038 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8303c : bv 32 := 0x00098513.
Lemma F_8303c : fetch_word Ubsan.M.loaded_segments (0x83094 : word) = Some W_8303c.
Proof. vm_refl. Qed.
Lemma D_8303c : decode_any W_8303c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83040 : bv 32 := 0x00000693.
Lemma F_83040 : fetch_word Ubsan.M.loaded_segments (0x83098 : word) = Some W_83040.
Proof. vm_refl. Qed.
Lemma D_83040 : decode_any W_83040 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83044 : bv 32 := 0x939e00ef.
Lemma F_83044 : fetch_word Ubsan.M.loaded_segments (0x8309c : word) = Some W_83044.
Proof. vm_refl. Qed.
Lemma D_83044 : decode_any W_83044 = Some (Jal 1 1968440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83048 : bv 32 := 0x00100513.
Lemma F_83048 : fetch_word Ubsan.M.loaded_segments (0x830a0 : word) = Some W_83048.
Proof. vm_refl. Qed.
Lemma D_83048 : decode_any W_83048 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8304c : bv 32 := 0x05454663.
Lemma F_8304c : fetch_word Ubsan.M.loaded_segments (0x830a4 : word) = Some W_8304c.
Proof. vm_refl. Qed.
Lemma D_8304c : decode_any W_8304c = Some (Branch BC_LT 10 20 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83050 : bv 32 := 0x080a1663.
Lemma F_83050 : fetch_word Ubsan.M.loaded_segments (0x830a8 : word) = Some W_83050.
Proof. vm_refl. Qed.
Lemma D_83050 : decode_any W_83050 = Some (Branch BC_NE 20 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83054 : bv 32 := 0x00c12503.
Lemma F_83054 : fetch_word Ubsan.M.loaded_segments (0x830ac : word) = Some W_83054.
Proof. vm_refl. Qed.
Lemma D_83054 : decode_any W_83054 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83058 : bv 32 := 0x02a95663.
Lemma F_83058 : fetch_word Ubsan.M.loaded_segments (0x830b0 : word) = Some W_83058.
Proof. vm_refl. Qed.
Lemma D_83058 : decode_any W_83058 = Some (Branch BC_GE 18 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8305c : bv 32 := 0x00410693.
Lemma F_8305c : fetch_word Ubsan.M.loaded_segments (0x830b4 : word) = Some W_8305c.
Proof. vm_refl. Qed.
Lemma D_8305c : decode_any W_8305c = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83060 : bv 32 := 0x00098513.
Lemma F_83060 : fetch_word Ubsan.M.loaded_segments (0x830b8 : word) = Some W_83060.
Proof. vm_refl. Qed.
Lemma D_83060 : decode_any W_83060 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83064 : bv 32 := 0x00090593.
Lemma F_83064 : fetch_word Ubsan.M.loaded_segments (0x830bc : word) = Some W_83064.
Proof. vm_refl. Qed.
Lemma D_83064 : decode_any W_83064 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83068 : bv 32 := 0x00048613.
Lemma F_83068 : fetch_word Ubsan.M.loaded_segments (0x830c0 : word) = Some W_83068.
Proof. vm_refl. Qed.
Lemma D_83068 : decode_any W_83068 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8306c : bv 32 := 0x8a9e10ef.
Lemma F_8306c : fetch_word Ubsan.M.loaded_segments (0x830c4 : word) = Some W_8306c.
Proof. vm_refl. Qed.
Lemma D_8306c : decode_any W_8306c = Some (Jal 1 1972392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83070 : bv 32 := 0x00412503.
Lemma F_83070 : fetch_word Ubsan.M.loaded_segments (0x830c8 : word) = Some W_83070.
Proof. vm_refl. Qed.
Lemma D_83070 : decode_any W_83070 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83074 : bv 32 := 0x00050863.
Lemma F_83074 : fetch_word Ubsan.M.loaded_segments (0x830cc : word) = Some W_83074.
Proof. vm_refl. Qed.
Lemma D_83074 : decode_any W_83074 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83078 : bv 32 := 0x00c12503.
Lemma F_83078 : fetch_word Ubsan.M.loaded_segments (0x830d0 : word) = Some W_83078.
Proof. vm_refl. Qed.
Lemma D_83078 : decode_any W_83078 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8307c : bv 32 := 0x0019091b.
Lemma F_8307c : fetch_word Ubsan.M.loaded_segments (0x830d4 : word) = Some W_8307c.
Proof. vm_refl. Qed.
Lemma D_8307c : decode_any W_8307c = Some (OpImm32 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83080 : bv 32 := 0xfca94ee3.
Lemma F_83080 : fetch_word Ubsan.M.loaded_segments (0x830d8 : word) = Some W_83080.
Proof. vm_refl. Qed.
Lemma D_83080 : decode_any W_83080 = Some (Branch BC_LT 18 10 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83084 : bv 32 := 0xfff9059b.
Lemma F_83084 : fetch_word Ubsan.M.loaded_segments (0x830dc : word) = Some W_83084.
Proof. vm_refl. Qed.
Lemma D_83084 : decode_any W_83084 = Some (OpImm32 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83088 : bv 32 := 0x0d25dc63.
Lemma F_83088 : fetch_word Ubsan.M.loaded_segments (0x830e0 : word) = Some W_83088.
Proof. vm_refl. Qed.
Lemma D_83088 : decode_any W_83088 = Some (Branch BC_GE 11 18 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8308c : bv 32 := 0x00000513.
Lemma F_8308c : fetch_word Ubsan.M.loaded_segments (0x830e4 : word) = Some W_8308c.
Proof. vm_refl. Qed.
Lemma D_8308c : decode_any W_8308c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83090 : bv 32 := 0x00b42023.
Lemma F_83090 : fetch_word Ubsan.M.loaded_segments (0x830e8 : word) = Some W_83090.
Proof. vm_refl. Qed.
Lemma D_83090 : decode_any W_83090 = Some (Store SZ4 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83094 : bv 32 := 0xf81ff06f.
Lemma F_83094 : fetch_word Ubsan.M.loaded_segments (0x830ec : word) = Some W_83094.
Proof. vm_refl. Qed.
Lemma D_83094 : decode_any W_83094 = Some (Jal 0 2097024, 4%Z).
Proof. vm_refl. Qed.

