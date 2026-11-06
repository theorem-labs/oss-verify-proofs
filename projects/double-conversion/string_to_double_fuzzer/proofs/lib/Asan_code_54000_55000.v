(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation ASEGS_I := ImgA.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_548e4 : bv 32 := 0x00195593.
Lemma F_548e4 : fetch_word ASEGS_I (0x548e4 : word) = Some W_548e4.
Proof. vm_refl. Qed.
Lemma D_548e4 : decode_any W_548e4 = Some (ShiftImm ALU_SRL 11 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548e8 : bv 32 := 0x55555637.
Lemma F_548e8 : fetch_word ASEGS_I (0x548e8 : word) = Some W_548e8.
Proof. vm_refl. Qed.
Lemma D_548e8 : decode_any W_548e8 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548ec : bv 32 := 0x33333737.
Lemma F_548ec : fetch_word ASEGS_I (0x548ec : word) = Some W_548ec.
Proof. vm_refl. Qed.
Lemma D_548ec : decode_any W_548ec = Some (Lui 14 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548f0 : bv 32 := 0x0f0f17b7.
Lemma F_548f0 : fetch_word ASEGS_I (0x548f0 : word) = Some W_548f0.
Proof. vm_refl. Qed.
Lemma D_548f0 : decode_any W_548f0 = Some (Lui 15 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548f4 : bv 32 := 0x00b965b3.
Lemma F_548f4 : fetch_word ASEGS_I (0x548f4 : word) = Some W_548f4.
Proof. vm_refl. Qed.
Lemma D_548f4 : decode_any W_548f4 = Some (Op ALU_OR 11 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548f8 : bv 32 := 0x5556061b.
Lemma F_548f8 : fetch_word ASEGS_I (0x548f8 : word) = Some W_548f8.
Proof. vm_refl. Qed.
Lemma D_548f8 : decode_any W_548f8 = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_548fc : bv 32 := 0x3337071b.
Lemma F_548fc : fetch_word ASEGS_I (0x548fc : word) = Some W_548fc.
Proof. vm_refl. Qed.
Lemma D_548fc : decode_any W_548fc = Some (OpImm32 14 14 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54900 : bv 32 := 0xf0f7879b.
Lemma F_54900 : fetch_word ASEGS_I (0x54900 : word) = Some W_54900.
Proof. vm_refl. Qed.
Lemma D_54900 : decode_any W_54900 = Some (OpImm32 15 15 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54904 : bv 32 := 0x0025d813.
Lemma F_54904 : fetch_word ASEGS_I (0x54904 : word) = Some W_54904.
Proof. vm_refl. Qed.
Lemma D_54904 : decode_any W_54904 = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54908 : bv 32 := 0x0105e5b3.
Lemma F_54908 : fetch_word ASEGS_I (0x54908 : word) = Some W_54908.
Proof. vm_refl. Qed.
Lemma D_54908 : decode_any W_54908 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5490c : bv 32 := 0x02061813.
Lemma F_5490c : fetch_word ASEGS_I (0x5490c : word) = Some W_5490c.
Proof. vm_refl. Qed.
Lemma D_5490c : decode_any W_5490c = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54910 : bv 32 := 0x01060633.
Lemma F_54910 : fetch_word ASEGS_I (0x54910 : word) = Some W_54910.
Proof. vm_refl. Qed.
Lemma D_54910 : decode_any W_54910 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54914 : bv 32 := 0x02071813.
Lemma F_54914 : fetch_word ASEGS_I (0x54914 : word) = Some W_54914.
Proof. vm_refl. Qed.
Lemma D_54914 : decode_any W_54914 = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54918 : bv 32 := 0x01070733.
Lemma F_54918 : fetch_word ASEGS_I (0x54918 : word) = Some W_54918.
Proof. vm_refl. Qed.
Lemma D_54918 : decode_any W_54918 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5491c : bv 32 := 0x02079813.
Lemma F_5491c : fetch_word ASEGS_I (0x5491c : word) = Some W_5491c.
Proof. vm_refl. Qed.
Lemma D_5491c : decode_any W_5491c = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54920 : bv 32 := 0x010787b3.
Lemma F_54920 : fetch_word ASEGS_I (0x54920 : word) = Some W_54920.
Proof. vm_refl. Qed.
Lemma D_54920 : decode_any W_54920 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54924 : bv 32 := 0x0045d813.
Lemma F_54924 : fetch_word ASEGS_I (0x54924 : word) = Some W_54924.
Proof. vm_refl. Qed.
Lemma D_54924 : decode_any W_54924 = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54928 : bv 32 := 0x0105e5b3.
Lemma F_54928 : fetch_word ASEGS_I (0x54928 : word) = Some W_54928.
Proof. vm_refl. Qed.
Lemma D_54928 : decode_any W_54928 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5492c : bv 32 := 0x0085d813.
Lemma F_5492c : fetch_word ASEGS_I (0x5492c : word) = Some W_5492c.
Proof. vm_refl. Qed.
Lemma D_5492c : decode_any W_5492c = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54930 : bv 32 := 0x0105e5b3.
Lemma F_54930 : fetch_word ASEGS_I (0x54930 : word) = Some W_54930.
Proof. vm_refl. Qed.
Lemma D_54930 : decode_any W_54930 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54934 : bv 32 := 0x0105d813.
Lemma F_54934 : fetch_word ASEGS_I (0x54934 : word) = Some W_54934.
Proof. vm_refl. Qed.
Lemma D_54934 : decode_any W_54934 = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54938 : bv 32 := 0x0105e5b3.
Lemma F_54938 : fetch_word ASEGS_I (0x54938 : word) = Some W_54938.
Proof. vm_refl. Qed.
Lemma D_54938 : decode_any W_54938 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5493c : bv 32 := 0x0205d813.
Lemma F_5493c : fetch_word ASEGS_I (0x5493c : word) = Some W_5493c.
Proof. vm_refl. Qed.
Lemma D_5493c : decode_any W_5493c = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54940 : bv 32 := 0x0105e5b3.
Lemma F_54940 : fetch_word ASEGS_I (0x54940 : word) = Some W_54940.
Proof. vm_refl. Qed.
Lemma D_54940 : decode_any W_54940 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54944 : bv 32 := 0xfff5c593.
Lemma F_54944 : fetch_word ASEGS_I (0x54944 : word) = Some W_54944.
Proof. vm_refl. Qed.
Lemma D_54944 : decode_any W_54944 = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54948 : bv 32 := 0x0015d813.
Lemma F_54948 : fetch_word ASEGS_I (0x54948 : word) = Some W_54948.
Proof. vm_refl. Qed.
Lemma D_54948 : decode_any W_54948 = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5494c : bv 32 := 0x00c87633.
Lemma F_5494c : fetch_word ASEGS_I (0x5494c : word) = Some W_5494c.
Proof. vm_refl. Qed.
Lemma D_5494c : decode_any W_5494c = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54950 : bv 32 := 0x01010837.
Lemma F_54950 : fetch_word ASEGS_I (0x54950 : word) = Some W_54950.
Proof. vm_refl. Qed.
Lemma D_54950 : decode_any W_54950 = Some (Lui 16 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54954 : bv 32 := 0x40c585b3.
Lemma F_54954 : fetch_word ASEGS_I (0x54954 : word) = Some W_54954.
Proof. vm_refl. Qed.
Lemma D_54954 : decode_any W_54954 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54958 : bv 32 := 0x0025d613.
Lemma F_54958 : fetch_word ASEGS_I (0x54958 : word) = Some W_54958.
Proof. vm_refl. Qed.
Lemma D_54958 : decode_any W_54958 = Some (ShiftImm ALU_SRL 12 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5495c : bv 32 := 0x00e5f5b3.
Lemma F_5495c : fetch_word ASEGS_I (0x5495c : word) = Some W_5495c.
Proof. vm_refl. Qed.
Lemma D_5495c : decode_any W_5495c = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54960 : bv 32 := 0x00e67633.
Lemma F_54960 : fetch_word ASEGS_I (0x54960 : word) = Some W_54960.
Proof. vm_refl. Qed.
Lemma D_54960 : decode_any W_54960 = Some (Op ALU_AND 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54964 : bv 32 := 0x0304b703.
Lemma F_54964 : fetch_word ASEGS_I (0x54964 : word) = Some W_54964.
Proof. vm_refl. Qed.
Lemma D_54964 : decode_any W_54964 = Some (Load SZ8 true 14 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54968 : bv 32 := 0x1018081b.
Lemma F_54968 : fetch_word ASEGS_I (0x54968 : word) = Some W_54968.
Proof. vm_refl. Qed.
Lemma D_54968 : decode_any W_54968 = Some (OpImm32 16 16 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5496c : bv 32 := 0x00c585b3.
Lemma F_5496c : fetch_word ASEGS_I (0x5496c : word) = Some W_5496c.
Proof. vm_refl. Qed.
Lemma D_5496c : decode_any W_5496c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54970 : bv 32 := 0x0045d613.
Lemma F_54970 : fetch_word ASEGS_I (0x54970 : word) = Some W_54970.
Proof. vm_refl. Qed.
Lemma D_54970 : decode_any W_54970 = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54974 : bv 32 := 0x00c585b3.
Lemma F_54974 : fetch_word ASEGS_I (0x54974 : word) = Some W_54974.
Proof. vm_refl. Qed.
Lemma D_54974 : decode_any W_54974 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54978 : bv 32 := 0x02081613.
Lemma F_54978 : fetch_word ASEGS_I (0x54978 : word) = Some W_54978.
Proof. vm_refl. Qed.
Lemma D_54978 : decode_any W_54978 = Some (ShiftImm ALU_SLL 12 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5497c : bv 32 := 0x00f5f5b3.
Lemma F_5497c : fetch_word ASEGS_I (0x5497c : word) = Some W_5497c.
Proof. vm_refl. Qed.
Lemma D_5497c : decode_any W_5497c = Some (Op ALU_AND 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54980 : bv 32 := 0x00c80633.
Lemma F_54980 : fetch_word ASEGS_I (0x54980 : word) = Some W_54980.
Proof. vm_refl. Qed.
Lemma D_54980 : decode_any W_54980 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54984 : bv 32 := 0x02c585b3.
Lemma F_54984 : fetch_word ASEGS_I (0x54984 : word) = Some W_54984.
Proof. vm_refl. Qed.
Lemma D_54984 : decode_any W_54984 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54988 : bv 32 := 0x0385d993.
Lemma F_54988 : fetch_word ASEGS_I (0x54988 : word) = Some W_54988.
Proof. vm_refl. Qed.
Lemma D_54988 : decode_any W_54988 = Some (ShiftImm ALU_SRL 19 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5498c : bv 32 := 0x1ce68c63.
Lemma F_5498c : fetch_word ASEGS_I (0x5498c : word) = Some W_5498c.
Proof. vm_refl. Qed.
Lemma D_5498c : decode_any W_5498c = Some (Branch BC_EQ 13 14 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54990 : bv 32 := 0x0084b603.
Lemma F_54990 : fetch_word ASEGS_I (0x54990 : word) = Some W_54990.
Proof. vm_refl. Qed.
Lemma D_54990 : decode_any W_54990 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54994 : bv 32 := 0x03f9c593.
Lemma F_54994 : fetch_word ASEGS_I (0x54994 : word) = Some W_54994.
Proof. vm_refl. Qed.
Lemma D_54994 : decode_any W_54994 = Some (OpImm ALU_XOR 11 19 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54998 : bv 32 := 0x00dabc23.
Lemma F_54998 : fetch_word ASEGS_I (0x54998 : word) = Some W_54998.
Proof. vm_refl. Qed.
Lemma D_54998 : decode_any W_54998 = Some (Store SZ8 21 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5499c : bv 32 := 0x00369713.
Lemma F_5499c : fetch_word ASEGS_I (0x5499c : word) = Some W_5499c.
Proof. vm_refl. Qed.
Lemma D_5499c : decode_any W_5499c = Some (ShiftImm ALU_SLL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549a0 : bv 32 := 0x00e60633.
Lemma F_549a0 : fetch_word ASEGS_I (0x549a0 : word) = Some W_549a0.
Proof. vm_refl. Qed.
Lemma D_549a0 : decode_any W_549a0 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549a4 : bv 32 := 0x01563023.
Lemma F_549a4 : fetch_word ASEGS_I (0x549a4 : word) = Some W_549a4.
Proof. vm_refl. Qed.
Lemma D_549a4 : decode_any W_549a4 = Some (Store SZ8 12 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549a8 : bv 32 := 0x0484b703.
Lemma F_549a8 : fetch_word ASEGS_I (0x549a8 : word) = Some W_549a8.
Proof. vm_refl. Qed.
Lemma D_549a8 : decode_any W_549a8 = Some (Load SZ8 true 14 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549ac : bv 32 := 0x0584b783.
Lemma F_549ac : fetch_word ASEGS_I (0x549ac : word) = Some W_549ac.
Proof. vm_refl. Qed.
Lemma D_549ac : decode_any W_549ac = Some (Load SZ8 true 15 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549b0 : bv 32 := 0x00168813.
Lemma F_549b0 : fetch_word ASEGS_I (0x549b0 : word) = Some W_549b0.
Proof. vm_refl. Qed.
Lemma D_549b0 : decode_any W_549b0 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549b4 : bv 32 := 0x0604b603.
Lemma F_549b4 : fetch_word ASEGS_I (0x549b4 : word) = Some W_549b4.
Proof. vm_refl. Qed.
Lemma D_549b4 : decode_any W_549b4 = Some (Load SZ8 true 12 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549b8 : bv 32 := 0x00170713.
Lemma F_549b8 : fetch_word ASEGS_I (0x549b8 : word) = Some W_549b8.
Proof. vm_refl. Qed.
Lemma D_549b8 : decode_any W_549b8 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549bc : bv 32 := 0x012786b3.
Lemma F_549bc : fetch_word ASEGS_I (0x549bc : word) = Some W_549bc.
Proof. vm_refl. Qed.
Lemma D_549bc : decode_any W_549bc = Some (Op ALU_ADD 13 15 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549c0 : bv 32 := 0x0304bc23.
Lemma F_549c0 : fetch_word ASEGS_I (0x549c0 : word) = Some W_549c0.
Proof. vm_refl. Qed.
Lemma D_549c0 : decode_any W_549c0 = Some (Store SZ8 9 16 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549c4 : bv 32 := 0x04048023.
Lemma F_549c4 : fetch_word ASEGS_I (0x549c4 : word) = Some W_549c4.
Proof. vm_refl. Qed.
Lemma D_549c4 : decode_any W_549c4 = Some (Store SZ1 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549c8 : bv 32 := 0x04e4b423.
Lemma F_549c8 : fetch_word ASEGS_I (0x549c8 : word) = Some W_549c8.
Proof. vm_refl. Qed.
Lemma D_549c8 : decode_any W_549c8 = Some (Store SZ8 9 14 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549cc : bv 32 := 0x04d4bc23.
Lemma F_549cc : fetch_word ASEGS_I (0x549cc : word) = Some W_549cc.
Proof. vm_refl. Qed.
Lemma D_549cc : decode_any W_549cc = Some (Store SZ8 9 13 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549d0 : bv 32 := 0x00c6e463.
Lemma F_549d0 : fetch_word ASEGS_I (0x549d0 : word) = Some W_549d0.
Proof. vm_refl. Qed.
Lemma D_549d0 : decode_any W_549d0 = Some (Branch BC_LTU 13 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549d4 : bv 32 := 0x00068613.
Lemma F_549d4 : fetch_word ASEGS_I (0x549d4 : word) = Some W_549d4.
Proof. vm_refl. Qed.
Lemma D_549d4 : decode_any W_549d4 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549d8 : bv 32 := 0x00359593.
Lemma F_549d8 : fetch_word ASEGS_I (0x549d8 : word) = Some W_549d8.
Proof. vm_refl. Qed.
Lemma D_549d8 : decode_any W_549d8 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549dc : bv 32 := 0x00b485b3.
Lemma F_549dc : fetch_word ASEGS_I (0x549dc : word) = Some W_549dc.
Proof. vm_refl. Qed.
Lemma D_549dc : decode_any W_549dc = Some (Op ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549e0 : bv 32 := 0x0685b683.
Lemma F_549e0 : fetch_word ASEGS_I (0x549e0 : word) = Some W_549e0.
Proof. vm_refl. Qed.
Lemma D_549e0 : decode_any W_549e0 = Some (Load SZ8 true 13 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549e4 : bv 32 := 0x00168693.
Lemma F_549e4 : fetch_word ASEGS_I (0x549e4 : word) = Some W_549e4.
Proof. vm_refl. Qed.
Lemma D_549e4 : decode_any W_549e4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549e8 : bv 32 := 0x06c4b023.
Lemma F_549e8 : fetch_word ASEGS_I (0x549e8 : word) = Some W_549e8.
Proof. vm_refl. Qed.
Lemma D_549e8 : decode_any W_549e8 = Some (Store SZ8 9 12 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_549ec : bv 32 := 0x06d5b423.
Lemma F_549ec : fetch_word ASEGS_I (0x549ec : word) = Some W_549ec.
Proof. vm_refl. Qed.
Lemma D_549ec : decode_any W_549ec = Some (Store SZ8 11 13 104, 4%Z).
Proof. vm_refl. Qed.
