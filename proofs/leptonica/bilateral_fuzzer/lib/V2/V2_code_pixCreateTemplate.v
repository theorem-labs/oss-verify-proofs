(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1990c : bv 32 := 0xff010113.
Lemma F_1990c : fetch_word Ubsan.M.loaded_segments (0x1990c : word) = Some W_1990c.
Proof. vm_refl. Qed.
Lemma D_1990c : decode_any W_1990c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_19910 : bv 32 := 0x00113423.
Lemma F_19910 : fetch_word Ubsan.M.loaded_segments (0x19910 : word) = Some W_19910.
Proof. vm_refl. Qed.
Lemma D_19910 : decode_any W_19910 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19914 : bv 32 := 0x00813023.
Lemma F_19914 : fetch_word Ubsan.M.loaded_segments (0x19914 : word) = Some W_19914.
Proof. vm_refl. Qed.
Lemma D_19914 : decode_any W_19914 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19918 : bv 32 := 0x04050663.
Lemma F_19918 : fetch_word Ubsan.M.loaded_segments (0x19918 : word) = Some W_19918.
Proof. vm_refl. Qed.
Lemma D_19918 : decode_any W_19918 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_1991c : bv 32 := 0x0c0000ef.
Lemma F_1991c : fetch_word Ubsan.M.loaded_segments (0x1991c : word) = Some W_1991c.
Proof. vm_refl. Qed.
Lemma D_1991c : decode_any W_1991c = Some (Jal 1 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_19920 : bv 32 := 0x06050663.
Lemma F_19920 : fetch_word Ubsan.M.loaded_segments (0x19920 : word) = Some W_19920.
Proof. vm_refl. Qed.
Lemma D_19920 : decode_any W_19920 = Some (Branch BC_EQ 10 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_19924 : bv 32 := 0x00757593.
Lemma F_19924 : fetch_word Ubsan.M.loaded_segments (0x19924 : word) = Some W_19924.
Proof. vm_refl. Qed.
Lemma D_19924 : decode_any W_19924 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_19928 : bv 32 := 0x0a059863.
Lemma F_19928 : fetch_word Ubsan.M.loaded_segments (0x19928 : word) = Some W_19928.
Proof. vm_refl. Qed.
Lemma D_19928 : decode_any W_19928 = Some (Branch BC_NE 11 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_1992c : bv 32 := 0x01056583.
Lemma F_1992c : fetch_word Ubsan.M.loaded_segments (0x1992c : word) = Some W_1992c.
Proof. vm_refl. Qed.
Lemma D_1992c : decode_any W_1992c = Some (Load SZ4 false 11 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19930 : bv 32 := 0x00456603.
Lemma F_19930 : fetch_word Ubsan.M.loaded_segments (0x19930 : word) = Some W_19930.
Proof. vm_refl. Qed.
Lemma D_19930 : decode_any W_19930 = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_19934 : bv 32 := 0x00259593.
Lemma F_19934 : fetch_word Ubsan.M.loaded_segments (0x19934 : word) = Some W_19934.
Proof. vm_refl. Qed.
Lemma D_19934 : decode_any W_19934 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_19938 : bv 32 := 0x02c596b3.
Lemma F_19938 : fetch_word Ubsan.M.loaded_segments (0x19938 : word) = Some W_19938.
Proof. vm_refl. Qed.
Lemma D_19938 : decode_any W_19938 = Some (Mul M_MULH 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1993c : bv 32 := 0x02c58633.
Lemma F_1993c : fetch_word Ubsan.M.loaded_segments (0x1993c : word) = Some W_1993c.
Proof. vm_refl. Qed.
Lemma D_1993c : decode_any W_1993c = Some (Mul M_MUL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19940 : bv 32 := 0x43f65593.
Lemma F_19940 : fetch_word Ubsan.M.loaded_segments (0x19940 : word) = Some W_19940.
Proof. vm_refl. Qed.
Lemma D_19940 : decode_any W_19940 = Some (ShiftImm ALU_SRA 11 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_19944 : bv 32 := 0x08b69a63.
Lemma F_19944 : fetch_word Ubsan.M.loaded_segments (0x19944 : word) = Some W_19944.
Proof. vm_refl. Qed.
Lemma D_19944 : decode_any W_19944 = Some (Branch BC_NE 13 11 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_19948 : bv 32 := 0x03853583.
Lemma F_19948 : fetch_word Ubsan.M.loaded_segments (0x19948 : word) = Some W_19948.
Proof. vm_refl. Qed.
Lemma D_19948 : decode_any W_19948 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1994c : bv 32 := 0x00050413.
Lemma F_1994c : fetch_word Ubsan.M.loaded_segments (0x1994c : word) = Some W_1994c.
Proof. vm_refl. Qed.
Lemma D_1994c : decode_any W_1994c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19950 : bv 32 := 0x00058513.
Lemma F_19950 : fetch_word Ubsan.M.loaded_segments (0x19950 : word) = Some W_19950.
Proof. vm_refl. Qed.
Lemma D_19950 : decode_any W_19950 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19954 : bv 32 := 0x00000593.
Lemma F_19954 : fetch_word Ubsan.M.loaded_segments (0x19954 : word) = Some W_19954.
Proof. vm_refl. Qed.
Lemma D_19954 : decode_any W_19954 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19958 : bv 32 := 0x729290ef.
Lemma F_19958 : fetch_word Ubsan.M.loaded_segments (0x19958 : word) = Some W_19958.
Proof. vm_refl. Qed.
Lemma D_19958 : decode_any W_19958 = Some (Jal 1 171816, 4%Z).
Proof. vm_refl. Qed.

Definition W_1995c : bv 32 := 0x00040513.
Lemma F_1995c : fetch_word Ubsan.M.loaded_segments (0x1995c : word) = Some W_1995c.
Proof. vm_refl. Qed.
Lemma D_1995c : decode_any W_1995c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19960 : bv 32 := 0x0680006f.
Lemma F_19960 : fetch_word Ubsan.M.loaded_segments (0x19960 : word) = Some W_19960.
Proof. vm_refl. Qed.
Lemma D_19960 : decode_any W_19960 = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_19964 : bv 32 := 0x0002b517.
Lemma F_19964 : fetch_word Ubsan.M.loaded_segments (0x19964 : word) = Some W_19964.
Proof. vm_refl. Qed.
Lemma D_19964 : decode_any W_19964 = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_19968 : bv 32 := 0x53453503.
Lemma F_19968 : fetch_word Ubsan.M.loaded_segments (0x19968 : word) = Some W_19968.
Proof. vm_refl. Qed.
Lemma D_19968 : decode_any W_19968 = Some (Load SZ8 true 10 10 1332, 4%Z).
Proof. vm_refl. Qed.

Definition W_1996c : bv 32 := 0x00052503.
Lemma F_1996c : fetch_word Ubsan.M.loaded_segments (0x1996c : word) = Some W_1996c.
Proof. vm_refl. Qed.
Lemma D_1996c : decode_any W_1996c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19970 : bv 32 := 0x00500593.
Lemma F_19970 : fetch_word Ubsan.M.loaded_segments (0x19970 : word) = Some W_19970.
Proof. vm_refl. Qed.
Lemma D_19970 : decode_any W_19970 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19974 : bv 32 := 0x04a5c863.
Lemma F_19974 : fetch_word Ubsan.M.loaded_segments (0x19974 : word) = Some W_19974.
Proof. vm_refl. Qed.
Lemma D_19974 : decode_any W_19974 = Some (Branch BC_LT 11 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_19978 : bv 32 := 0xffff7517.
Lemma F_19978 : fetch_word Ubsan.M.loaded_segments (0x19978 : word) = Some W_19978.
Proof. vm_refl. Qed.
Lemma D_19978 : decode_any W_19978 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_1997c : bv 32 := 0xffff8597.
Lemma F_1997c : fetch_word Ubsan.M.loaded_segments (0x1997c : word) = Some W_1997c.
Proof. vm_refl. Qed.
Lemma D_1997c : decode_any W_1997c = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_19980 : bv 32 := 0x93c50513.
Lemma F_19980 : fetch_word Ubsan.M.loaded_segments (0x19980 : word) = Some W_19980.
Proof. vm_refl. Qed.
Lemma D_19980 : decode_any W_19980 = Some (OpImm ALU_ADD 10 10 2364, 4%Z).
Proof. vm_refl. Qed.

Definition W_19984 : bv 32 := 0xe6c58593.
Lemma F_19984 : fetch_word Ubsan.M.loaded_segments (0x19984 : word) = Some W_19984.
Proof. vm_refl. Qed.
Lemma D_19984 : decode_any W_19984 = Some (OpImm ALU_ADD 11 11 3692, 4%Z).
Proof. vm_refl. Qed.

Definition W_19988 : bv 32 := 0x0280006f.
Lemma F_19988 : fetch_word Ubsan.M.loaded_segments (0x19988 : word) = Some W_19988.
Proof. vm_refl. Qed.
Lemma D_19988 : decode_any W_19988 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1998c : bv 32 := 0x0002b517.
Lemma F_1998c : fetch_word Ubsan.M.loaded_segments (0x1998c : word) = Some W_1998c.
Proof. vm_refl. Qed.
Lemma D_1998c : decode_any W_1998c = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_19990 : bv 32 := 0x50c53503.
Lemma F_19990 : fetch_word Ubsan.M.loaded_segments (0x19990 : word) = Some W_19990.
Proof. vm_refl. Qed.
Lemma D_19990 : decode_any W_19990 = Some (Load SZ8 true 10 10 1292, 4%Z).
Proof. vm_refl. Qed.

Definition W_19994 : bv 32 := 0x00052503.
Lemma F_19994 : fetch_word Ubsan.M.loaded_segments (0x19994 : word) = Some W_19994.
Proof. vm_refl. Qed.
Lemma D_19994 : decode_any W_19994 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19998 : bv 32 := 0x00500593.
Lemma F_19998 : fetch_word Ubsan.M.loaded_segments (0x19998 : word) = Some W_19998.
Proof. vm_refl. Qed.
Lemma D_19998 : decode_any W_19998 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1999c : bv 32 := 0x02a5c463.
Lemma F_1999c : fetch_word Ubsan.M.loaded_segments (0x1999c : word) = Some W_1999c.
Proof. vm_refl. Qed.
Lemma D_1999c : decode_any W_1999c = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_199a0 : bv 32 := 0xffff7517.
Lemma F_199a0 : fetch_word Ubsan.M.loaded_segments (0x199a0 : word) = Some W_199a0.
Proof. vm_refl. Qed.
Lemma D_199a0 : decode_any W_199a0 = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_199a4 : bv 32 := 0xffff8597.
Lemma F_199a4 : fetch_word Ubsan.M.loaded_segments (0x199a4 : word) = Some W_199a4.
Proof. vm_refl. Qed.
Lemma D_199a4 : decode_any W_199a4 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_199a8 : bv 32 := 0xdc550513.
Lemma F_199a8 : fetch_word Ubsan.M.loaded_segments (0x199a8 : word) = Some W_199a8.
Proof. vm_refl. Qed.
Lemma D_199a8 : decode_any W_199a8 = Some (OpImm ALU_ADD 10 10 3525, 4%Z).
Proof. vm_refl. Qed.

Definition W_199ac : bv 32 := 0xe4458593.
Lemma F_199ac : fetch_word Ubsan.M.loaded_segments (0x199ac : word) = Some W_199ac.
Proof. vm_refl. Qed.
Lemma D_199ac : decode_any W_199ac = Some (OpImm ALU_ADD 11 11 3652, 4%Z).
Proof. vm_refl. Qed.

Definition W_199b0 : bv 32 := 0x00000613.
Lemma F_199b0 : fetch_word Ubsan.M.loaded_segments (0x199b0 : word) = Some W_199b0.
Proof. vm_refl. Qed.
Lemma D_199b0 : decode_any W_199b0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_199b4 : bv 32 := 0x00813083.
Lemma F_199b4 : fetch_word Ubsan.M.loaded_segments (0x199b4 : word) = Some W_199b4.
Proof. vm_refl. Qed.
Lemma D_199b4 : decode_any W_199b4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_199b8 : bv 32 := 0x00013403.
Lemma F_199b8 : fetch_word Ubsan.M.loaded_segments (0x199b8 : word) = Some W_199b8.
Proof. vm_refl. Qed.
Lemma D_199b8 : decode_any W_199b8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_199bc : bv 32 := 0x01010113.
Lemma F_199bc : fetch_word Ubsan.M.loaded_segments (0x199bc : word) = Some W_199bc.
Proof. vm_refl. Qed.
Lemma D_199bc : decode_any W_199bc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_199c0 : bv 32 := 0xd04fe06f.
Lemma F_199c0 : fetch_word Ubsan.M.loaded_segments (0x199c0 : word) = Some W_199c0.
Proof. vm_refl. Qed.
Lemma D_199c0 : decode_any W_199c0 = Some (Jal 0 2090244, 4%Z).
Proof. vm_refl. Qed.

Definition W_199c4 : bv 32 := 0x00000513.
Lemma F_199c4 : fetch_word Ubsan.M.loaded_segments (0x199c4 : word) = Some W_199c4.
Proof. vm_refl. Qed.
Lemma D_199c4 : decode_any W_199c4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_199c8 : bv 32 := 0x00813083.
Lemma F_199c8 : fetch_word Ubsan.M.loaded_segments (0x199c8 : word) = Some W_199c8.
Proof. vm_refl. Qed.
Lemma D_199c8 : decode_any W_199c8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_199cc : bv 32 := 0x00013403.
Lemma F_199cc : fetch_word Ubsan.M.loaded_segments (0x199cc : word) = Some W_199cc.
Proof. vm_refl. Qed.
Lemma D_199cc : decode_any W_199cc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_199d0 : bv 32 := 0x01010113.
Lemma F_199d0 : fetch_word Ubsan.M.loaded_segments (0x199d0 : word) = Some W_199d0.
Proof. vm_refl. Qed.
Lemma D_199d0 : decode_any W_199d0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_199d4 : bv 32 := 0x00008067.
Lemma F_199d4 : fetch_word Ubsan.M.loaded_segments (0x199d4 : word) = Some W_199d4.
Proof. vm_refl. Qed.
Lemma D_199d4 : decode_any W_199d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_199d8 : bv 32 := 0xc0001073.
Lemma F_199d8 : fetch_word Ubsan.M.loaded_segments (0x199d8 : word) = Some W_199d8.
Proof. vm_refl. Qed.
Lemma D_199d8 : decode_any W_199d8 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
