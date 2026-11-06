(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
Unset Nia Cache.
Unset Lia Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_198d4 : bv 32 := 0xff010113.
Lemma F_198d4 : fetch_word Ubsan.M.loaded_segments (0x198d4 : word) = Some W_198d4.
Proof. vm_refl. Qed.
Lemma D_198d4 : decode_any W_198d4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_198d8 : bv 32 := 0x00113423.
Lemma F_198d8 : fetch_word Ubsan.M.loaded_segments (0x198d8 : word) = Some W_198d8.
Proof. vm_refl. Qed.
Lemma D_198d8 : decode_any W_198d8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_198dc : bv 32 := 0x00813023.
Lemma F_198dc : fetch_word Ubsan.M.loaded_segments (0x198dc : word) = Some W_198dc.
Proof. vm_refl. Qed.
Lemma D_198dc : decode_any W_198dc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_198e0 : bv 32 := 0x198000ef.
Lemma F_198e0 : fetch_word Ubsan.M.loaded_segments (0x198e0 : word) = Some W_198e0.
Proof. vm_refl. Qed.
Lemma D_198e0 : decode_any W_198e0 = Some (Jal 1 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_198e4 : bv 32 := 0x00053403.
Lemma F_198e4 : fetch_word Ubsan.M.loaded_segments (0x198e4 : word) = Some W_198e4.
Proof. vm_refl. Qed.
Lemma D_198e4 : decode_any W_198e4 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_198e8 : bv 32 := 0x12041663.
Lemma F_198e8 : fetch_word Ubsan.M.loaded_segments (0x198e8 : word) = Some W_198e8.
Proof. vm_refl. Qed.
Lemma D_198e8 : decode_any W_198e8 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_198ec : bv 32 := 0x00038517.
Lemma F_198ec : fetch_word Ubsan.M.loaded_segments (0x198ec : word) = Some W_198ec.
Proof. vm_refl. Qed.
Lemma D_198ec : decode_any W_198ec = Some (Auipc 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_198f0 : bv 32 := 0x29c53403.
Lemma F_198f0 : fetch_word Ubsan.M.loaded_segments (0x198f0 : word) = Some W_198f0.
Proof. vm_refl. Qed.
Lemma D_198f0 : decode_any W_198f0 = Some (Load SZ8 true 8 10 668, 4%Z).
Proof. vm_refl. Qed.

Definition W_198f4 : bv 32 := 0x04040a63.
Lemma F_198f4 : fetch_word Ubsan.M.loaded_segments (0x198f4 : word) = Some W_198f4.
Proof. vm_refl. Qed.
Lemma D_198f4 : decode_any W_198f4 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_19948 : bv 32 := 0x00008517.
Lemma F_19948 : fetch_word Ubsan.M.loaded_segments (0x19948 : word) = Some W_19948.
Proof. vm_refl. Qed.
Lemma D_19948 : decode_any W_19948 = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1994c : bv 32 := 0xa2853403.
Lemma F_1994c : fetch_word Ubsan.M.loaded_segments (0x1994c : word) = Some W_1994c.
Proof. vm_refl. Qed.
Lemma D_1994c : decode_any W_1994c = Some (Load SZ8 true 8 10 2600, 4%Z).
Proof. vm_refl. Qed.

Definition W_19950 : bv 32 := 0x04040a63.
Lemma F_19950 : fetch_word Ubsan.M.loaded_segments (0x19950 : word) = Some W_19950.
Proof. vm_refl. Qed.
Lemma D_19950 : decode_any W_19950 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_19954 : bv 32 := 0x08c42503.
Lemma F_19954 : fetch_word Ubsan.M.loaded_segments (0x19954 : word) = Some W_19954.
Proof. vm_refl. Qed.
Lemma D_19954 : decode_any W_19954 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_19958 : bv 32 := 0x00054663.
Lemma F_19958 : fetch_word Ubsan.M.loaded_segments (0x19958 : word) = Some W_19958.
Proof. vm_refl. Qed.
Lemma D_19958 : decode_any W_19958 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19964 : bv 32 := 0x02843503.
Lemma F_19964 : fetch_word Ubsan.M.loaded_segments (0x19964 : word) = Some W_19964.
Proof. vm_refl. Qed.
Lemma D_19964 : decode_any W_19964 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19968 : bv 32 := 0x03843583.
Lemma F_19968 : fetch_word Ubsan.M.loaded_segments (0x19968 : word) = Some W_19968.
Proof. vm_refl. Qed.
Lemma D_19968 : decode_any W_19968 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1996c : bv 32 := 0x00b50c63.
Lemma F_1996c : fetch_word Ubsan.M.loaded_segments (0x1996c : word) = Some W_1996c.
Proof. vm_refl. Qed.
Lemma D_1996c : decode_any W_1996c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19970 : bv 32 := 0x04843683.
Lemma F_19970 : fetch_word Ubsan.M.loaded_segments (0x19970 : word) = Some W_19970.
Proof. vm_refl. Qed.
Lemma D_19970 : decode_any W_19970 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_19974 : bv 32 := 0x00040513.
Lemma F_19974 : fetch_word Ubsan.M.loaded_segments (0x19974 : word) = Some W_19974.
Proof. vm_refl. Qed.
Lemma D_19974 : decode_any W_19974 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19978 : bv 32 := 0x00000593.
Lemma F_19978 : fetch_word Ubsan.M.loaded_segments (0x19978 : word) = Some W_19978.
Proof. vm_refl. Qed.
Lemma D_19978 : decode_any W_19978 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1997c : bv 32 := 0x00000613.
Lemma F_1997c : fetch_word Ubsan.M.loaded_segments (0x1997c : word) = Some W_1997c.
Proof. vm_refl. Qed.
Lemma D_1997c : decode_any W_1997c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19980 : bv 32 := 0x000680e7.
Lemma F_19980 : fetch_word Ubsan.M.loaded_segments (0x19980 : word) = Some W_19980.
Proof. vm_refl. Qed.
Lemma D_19980 : decode_any W_19980 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19984 : bv 32 := 0x00843503.
Lemma F_19984 : fetch_word Ubsan.M.loaded_segments (0x19984 : word) = Some W_19984.
Proof. vm_refl. Qed.
Lemma D_19984 : decode_any W_19984 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19988 : bv 32 := 0x01043583.
Lemma F_19988 : fetch_word Ubsan.M.loaded_segments (0x19988 : word) = Some W_19988.
Proof. vm_refl. Qed.
Lemma D_19988 : decode_any W_19988 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1998c : bv 32 := 0x00b50c63.
Lemma F_1998c : fetch_word Ubsan.M.loaded_segments (0x1998c : word) = Some W_1998c.
Proof. vm_refl. Qed.
Lemma D_1998c : decode_any W_1998c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_199a4 : bv 32 := 0x00008517.
Lemma F_199a4 : fetch_word Ubsan.M.loaded_segments (0x199a4 : word) = Some W_199a4.
Proof. vm_refl. Qed.
Lemma D_199a4 : decode_any W_199a4 = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_199a8 : bv 32 := 0x8dc53403.
Lemma F_199a8 : fetch_word Ubsan.M.loaded_segments (0x199a8 : word) = Some W_199a8.
Proof. vm_refl. Qed.
Lemma D_199a8 : decode_any W_199a8 = Some (Load SZ8 true 8 10 2268, 4%Z).
Proof. vm_refl. Qed.

Definition W_199ac : bv 32 := 0x0a040e63.
Lemma F_199ac : fetch_word Ubsan.M.loaded_segments (0x199ac : word) = Some W_199ac.
Proof. vm_refl. Qed.
Lemma D_199ac : decode_any W_199ac = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_199b0 : bv 32 := 0x08c42503.
Lemma F_199b0 : fetch_word Ubsan.M.loaded_segments (0x199b0 : word) = Some W_199b0.
Proof. vm_refl. Qed.
Lemma D_199b0 : decode_any W_199b0 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_199b4 : bv 32 := 0x00054663.
Lemma F_199b4 : fetch_word Ubsan.M.loaded_segments (0x199b4 : word) = Some W_199b4.
Proof. vm_refl. Qed.
Lemma D_199b4 : decode_any W_199b4 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_199c0 : bv 32 := 0x02843503.
Lemma F_199c0 : fetch_word Ubsan.M.loaded_segments (0x199c0 : word) = Some W_199c0.
Proof. vm_refl. Qed.
Lemma D_199c0 : decode_any W_199c0 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_199c4 : bv 32 := 0x03843583.
Lemma F_199c4 : fetch_word Ubsan.M.loaded_segments (0x199c4 : word) = Some W_199c4.
Proof. vm_refl. Qed.
Lemma D_199c4 : decode_any W_199c4 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_199c8 : bv 32 := 0x00b50c63.
Lemma F_199c8 : fetch_word Ubsan.M.loaded_segments (0x199c8 : word) = Some W_199c8.
Proof. vm_refl. Qed.
Lemma D_199c8 : decode_any W_199c8 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_199e0 : bv 32 := 0x00843503.
Lemma F_199e0 : fetch_word Ubsan.M.loaded_segments (0x199e0 : word) = Some W_199e0.
Proof. vm_refl. Qed.
Lemma D_199e0 : decode_any W_199e0 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_199e4 : bv 32 := 0x01043583.
Lemma F_199e4 : fetch_word Ubsan.M.loaded_segments (0x199e4 : word) = Some W_199e4.
Proof. vm_refl. Qed.
Lemma D_199e4 : decode_any W_199e4 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_199e8 : bv 32 := 0x08b50063.
Lemma F_199e8 : fetch_word Ubsan.M.loaded_segments (0x199e8 : word) = Some W_199e8.
Proof. vm_refl. Qed.
Lemma D_199e8 : decode_any W_199e8 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a68 : bv 32 := 0x00813083.
Lemma F_19a68 : fetch_word Ubsan.M.loaded_segments (0x19a68 : word) = Some W_19a68.
Proof. vm_refl. Qed.
Lemma D_19a68 : decode_any W_19a68 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a6c : bv 32 := 0x00013403.
Lemma F_19a6c : fetch_word Ubsan.M.loaded_segments (0x19a6c : word) = Some W_19a6c.
Proof. vm_refl. Qed.
Lemma D_19a6c : decode_any W_19a6c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a70 : bv 32 := 0x01010113.
Lemma F_19a70 : fetch_word Ubsan.M.loaded_segments (0x19a70 : word) = Some W_19a70.
Proof. vm_refl. Qed.
Lemma D_19a70 : decode_any W_19a70 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a74 : bv 32 := 0x00008067.
Lemma F_19a74 : fetch_word Ubsan.M.loaded_segments (0x19a74 : word) = Some W_19a74.
Proof. vm_refl. Qed.
Lemma D_19a74 : decode_any W_19a74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a78 : bv 32 := 0xff010113.
Lemma F_19a78 : fetch_word Ubsan.M.loaded_segments (0x19a78 : word) = Some W_19a78.
Proof. vm_refl. Qed.
Lemma D_19a78 : decode_any W_19a78 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a7c : bv 32 := 0x00113423.
Lemma F_19a7c : fetch_word Ubsan.M.loaded_segments (0x19a7c : word) = Some W_19a7c.
Proof. vm_refl. Qed.
Lemma D_19a7c : decode_any W_19a7c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a80 : bv 32 := 0x00813023.
Lemma F_19a80 : fetch_word Ubsan.M.loaded_segments (0x19a80 : word) = Some W_19a80.
Proof. vm_refl. Qed.
Lemma D_19a80 : decode_any W_19a80 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a84 : bv 32 := 0x00038517.
Lemma F_19a84 : fetch_word Ubsan.M.loaded_segments (0x19a84 : word) = Some W_19a84.
Proof. vm_refl. Qed.
Lemma D_19a84 : decode_any W_19a84 = Some (Auipc 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a88 : bv 32 := 0x10c50413.
Lemma F_19a88 : fetch_word Ubsan.M.loaded_segments (0x19a88 : word) = Some W_19a88.
Proof. vm_refl. Qed.
Lemma D_19a88 : decode_any W_19a88 = Some (OpImm ALU_ADD 8 10 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a8c : bv 32 := 0x00040513.
Lemma F_19a8c : fetch_word Ubsan.M.loaded_segments (0x19a8c : word) = Some W_19a8c.
Proof. vm_refl. Qed.
Lemma D_19a8c : decode_any W_19a8c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a90 : bv 32 := 0x258050ef.
Lemma F_19a90 : fetch_word Ubsan.M.loaded_segments (0x19a90 : word) = Some W_19a90.
Proof. vm_refl. Qed.
Lemma D_19a90 : decode_any W_19a90 = Some (Jal 1 21080, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a94 : bv 32 := 0x00840513.
Lemma F_19a94 : fetch_word Ubsan.M.loaded_segments (0x19a94 : word) = Some W_19a94.
Proof. vm_refl. Qed.
Lemma D_19a94 : decode_any W_19a94 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a98 : bv 32 := 0x00813083.
Lemma F_19a98 : fetch_word Ubsan.M.loaded_segments (0x19a98 : word) = Some W_19a98.
Proof. vm_refl. Qed.
Lemma D_19a98 : decode_any W_19a98 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19a9c : bv 32 := 0x00013403.
Lemma F_19a9c : fetch_word Ubsan.M.loaded_segments (0x19a9c : word) = Some W_19a9c.
Proof. vm_refl. Qed.
Lemma D_19a9c : decode_any W_19a9c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19aa0 : bv 32 := 0x01010113.
Lemma F_19aa0 : fetch_word Ubsan.M.loaded_segments (0x19aa0 : word) = Some W_19aa0.
Proof. vm_refl. Qed.
Lemma D_19aa0 : decode_any W_19aa0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19aa4 : bv 32 := 0x00008067.
Lemma F_19aa4 : fetch_word Ubsan.M.loaded_segments (0x19aa4 : word) = Some W_19aa4.
Proof. vm_refl. Qed.
Lemma D_19aa4 : decode_any W_19aa4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ab4 : bv 32 := 0x00008067.
Lemma F_19ab4 : fetch_word Ubsan.M.loaded_segments (0x19ab4 : word) = Some W_19ab4.
Proof. vm_refl. Qed.
Lemma D_19ab4 : decode_any W_19ab4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ae4 : bv 32 := 0xf9010113.
Lemma F_19ae4 : fetch_word Ubsan.M.loaded_segments (0x19ae4 : word) = Some W_19ae4.
Proof. vm_refl. Qed.
Lemma D_19ae4 : decode_any W_19ae4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ae8 : bv 32 := 0x06113423.
Lemma F_19ae8 : fetch_word Ubsan.M.loaded_segments (0x19ae8 : word) = Some W_19ae8.
Proof. vm_refl. Qed.
Lemma D_19ae8 : decode_any W_19ae8 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_19aec : bv 32 := 0x06813023.
Lemma F_19aec : fetch_word Ubsan.M.loaded_segments (0x19aec : word) = Some W_19aec.
Proof. vm_refl. Qed.
Lemma D_19aec : decode_any W_19aec = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_19af0 : bv 32 := 0x04913c23.
Lemma F_19af0 : fetch_word Ubsan.M.loaded_segments (0x19af0 : word) = Some W_19af0.
Proof. vm_refl. Qed.
Lemma D_19af0 : decode_any W_19af0 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_19af4 : bv 32 := 0x05213823.
Lemma F_19af4 : fetch_word Ubsan.M.loaded_segments (0x19af4 : word) = Some W_19af4.
Proof. vm_refl. Qed.
Lemma D_19af4 : decode_any W_19af4 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_19af8 : bv 32 := 0x05313423.
Lemma F_19af8 : fetch_word Ubsan.M.loaded_segments (0x19af8 : word) = Some W_19af8.
Proof. vm_refl. Qed.
Lemma D_19af8 : decode_any W_19af8 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_19afc : bv 32 := 0x05413023.
Lemma F_19afc : fetch_word Ubsan.M.loaded_segments (0x19afc : word) = Some W_19afc.
Proof. vm_refl. Qed.
Lemma D_19afc : decode_any W_19afc = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b00 : bv 32 := 0x03513c23.
Lemma F_19b00 : fetch_word Ubsan.M.loaded_segments (0x19b00 : word) = Some W_19b00.
Proof. vm_refl. Qed.
Lemma D_19b00 : decode_any W_19b00 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b04 : bv 32 := 0x03613823.
Lemma F_19b04 : fetch_word Ubsan.M.loaded_segments (0x19b04 : word) = Some W_19b04.
Proof. vm_refl. Qed.
Lemma D_19b04 : decode_any W_19b04 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b08 : bv 32 := 0x00060413.
Lemma F_19b08 : fetch_word Ubsan.M.loaded_segments (0x19b08 : word) = Some W_19b08.
Proof. vm_refl. Qed.
Lemma D_19b08 : decode_any W_19b08 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b0c : bv 32 := 0x00050493.
Lemma F_19b0c : fetch_word Ubsan.M.loaded_segments (0x19b0c : word) = Some W_19b0c.
Proof. vm_refl. Qed.
Lemma D_19b0c : decode_any W_19b0c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b10 : bv 32 := 0x00006517.
Lemma F_19b10 : fetch_word Ubsan.M.loaded_segments (0x19b10 : word) = Some W_19b10.
Proof. vm_refl. Qed.
Lemma D_19b10 : decode_any W_19b10 = Some (Auipc 10 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b14 : bv 32 := 0x64853a83.
Lemma F_19b14 : fetch_word Ubsan.M.loaded_segments (0x19b14 : word) = Some W_19b14.
Proof. vm_refl. Qed.
Lemma D_19b14 : decode_any W_19b14 = Some (Load SZ8 true 21 10 1608, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b18 : bv 32 := 0x000ab503.
Lemma F_19b18 : fetch_word Ubsan.M.loaded_segments (0x19b18 : word) = Some W_19b18.
Proof. vm_refl. Qed.
Lemma D_19b18 : decode_any W_19b18 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b1c : bv 32 := 0x02a13423.
Lemma F_19b1c : fetch_word Ubsan.M.loaded_segments (0x19b1c : word) = Some W_19b1c.
Proof. vm_refl. Qed.
Lemma D_19b1c : decode_any W_19b1c = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b20 : bv 32 := 0x0284b503.
Lemma F_19b20 : fetch_word Ubsan.M.loaded_segments (0x19b20 : word) = Some W_19b20.
Proof. vm_refl. Qed.
Lemma D_19b20 : decode_any W_19b20 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b24 : bv 32 := 0x0384b603.
Lemma F_19b24 : fetch_word Ubsan.M.loaded_segments (0x19b24 : word) = Some W_19b24.
Proof. vm_refl. Qed.
Lemma D_19b24 : decode_any W_19b24 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b28 : bv 32 := 0x40c50b33.
Lemma F_19b28 : fetch_word Ubsan.M.loaded_segments (0x19b28 : word) = Some W_19b28.
Proof. vm_refl. Qed.
Lemma D_19b28 : decode_any W_19b28 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b2c : bv 32 := 0x00c546b3.
Lemma F_19b2c : fetch_word Ubsan.M.loaded_segments (0x19b2c : word) = Some W_19b2c.
Proof. vm_refl. Qed.
Lemma D_19b2c : decode_any W_19b2c = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b30 : bv 32 := 0x00c13423.
Lemma F_19b30 : fetch_word Ubsan.M.loaded_segments (0x19b30 : word) = Some W_19b30.
Proof. vm_refl. Qed.
Lemma D_19b30 : decode_any W_19b30 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b34 : bv 32 := 0x01613823.
Lemma F_19b34 : fetch_word Ubsan.M.loaded_segments (0x19b34 : word) = Some W_19b34.
Proof. vm_refl. Qed.
Lemma D_19b34 : decode_any W_19b34 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b38 : bv 32 := 0x00b13c23.
Lemma F_19b38 : fetch_word Ubsan.M.loaded_segments (0x19b38 : word) = Some W_19b38.
Proof. vm_refl. Qed.
Lemma D_19b38 : decode_any W_19b38 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b3c : bv 32 := 0x02813023.
Lemma F_19b3c : fetch_word Ubsan.M.loaded_segments (0x19b3c : word) = Some W_19b3c.
Proof. vm_refl. Qed.
Lemma D_19b3c : decode_any W_19b3c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b40 : bv 32 := 0x008b0b33.
Lemma F_19b40 : fetch_word Ubsan.M.loaded_segments (0x19b40 : word) = Some W_19b40.
Proof. vm_refl. Qed.
Lemma D_19b40 : decode_any W_19b40 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b44 : bv 32 := 0x00d03933.
Lemma F_19b44 : fetch_word Ubsan.M.loaded_segments (0x19b44 : word) = Some W_19b44.
Proof. vm_refl. Qed.
Lemma D_19b44 : decode_any W_19b44 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b48 : bv 32 := 0x00c50663.
Lemma F_19b48 : fetch_word Ubsan.M.loaded_segments (0x19b48 : word) = Some W_19b48.
Proof. vm_refl. Qed.
Lemma D_19b48 : decode_any W_19b48 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b4c : bv 32 := 0x00810993.
Lemma F_19b4c : fetch_word Ubsan.M.loaded_segments (0x19b4c : word) = Some W_19b4c.
Proof. vm_refl. Qed.
Lemma D_19b4c : decode_any W_19b4c = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b50 : bv 32 := 0x0080006f.
Lemma F_19b50 : fetch_word Ubsan.M.loaded_segments (0x19b50 : word) = Some W_19b50.
Proof. vm_refl. Qed.
Lemma D_19b50 : decode_any W_19b50 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b54 : bv 32 := 0x01810993.
Lemma F_19b54 : fetch_word Ubsan.M.loaded_segments (0x19b54 : word) = Some W_19b54.
Proof. vm_refl. Qed.
Lemma D_19b54 : decode_any W_19b54 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b58 : bv 32 := 0x0784a503.
Lemma F_19b58 : fetch_word Ubsan.M.loaded_segments (0x19b58 : word) = Some W_19b58.
Proof. vm_refl. Qed.
Lemma D_19b58 : decode_any W_19b58 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b5c : bv 32 := 0x00190913.
Lemma F_19b5c : fetch_word Ubsan.M.loaded_segments (0x19b5c : word) = Some W_19b5c.
Proof. vm_refl. Qed.
Lemma D_19b5c : decode_any W_19b5c = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b60 : bv 32 := 0x04200893.
Lemma F_19b60 : fetch_word Ubsan.M.loaded_segments (0x19b60 : word) = Some W_19b60.
Proof. vm_refl. Qed.
Lemma D_19b60 : decode_any W_19b60 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b64 : bv 32 := 0x00098593.
Lemma F_19b64 : fetch_word Ubsan.M.loaded_segments (0x19b64 : word) = Some W_19b64.
Proof. vm_refl. Qed.
Lemma D_19b64 : decode_any W_19b64 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b68 : bv 32 := 0x00090613.
Lemma F_19b68 : fetch_word Ubsan.M.loaded_segments (0x19b68 : word) = Some W_19b68.
Proof. vm_refl. Qed.
Lemma D_19b68 : decode_any W_19b68 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b6c : bv 32 := 0x00000073.
Lemma F_19b6c : fetch_word Ubsan.M.loaded_segments (0x19b6c : word) = Some W_19b6c.
Proof. vm_refl. Qed.
Lemma D_19b6c : decode_any W_19b6c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_19b6c : is_ecall W_19b6c = true.
Proof. reflexivity. Qed.

Definition W_19b70 : bv 32 := 0xbadfd0ef.
Lemma F_19b70 : fetch_word Ubsan.M.loaded_segments (0x19b70 : word) = Some W_19b70.
Proof. vm_refl. Qed.
Lemma D_19b70 : decode_any W_19b70 = Some (Jal 1 2087852, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b74 : bv 32 := 0x09651863.
Lemma F_19b74 : fetch_word Ubsan.M.loaded_segments (0x19b74 : word) = Some W_19b74.
Proof. vm_refl. Qed.
Lemma D_19b74 : decode_any W_19b74 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b78 : bv 32 := 0x0584b503.
Lemma F_19b78 : fetch_word Ubsan.M.loaded_segments (0x19b78 : word) = Some W_19b78.
Proof. vm_refl. Qed.
Lemma D_19b78 : decode_any W_19b78 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b7c : bv 32 := 0x0604b583.
Lemma F_19b7c : fetch_word Ubsan.M.loaded_segments (0x19b7c : word) = Some W_19b7c.
Proof. vm_refl. Qed.
Lemma D_19b7c : decode_any W_19b7c = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b80 : bv 32 := 0x00b505b3.
Lemma F_19b80 : fetch_word Ubsan.M.loaded_segments (0x19b80 : word) = Some W_19b80.
Proof. vm_refl. Qed.
Lemma D_19b80 : decode_any W_19b80 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b84 : bv 32 := 0x02b4b023.
Lemma F_19b84 : fetch_word Ubsan.M.loaded_segments (0x19b84 : word) = Some W_19b84.
Proof. vm_refl. Qed.
Lemma D_19b84 : decode_any W_19b84 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b88 : bv 32 := 0x02a4b423.
Lemma F_19b88 : fetch_word Ubsan.M.loaded_segments (0x19b88 : word) = Some W_19b88.
Proof. vm_refl. Qed.
Lemma D_19b88 : decode_any W_19b88 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b8c : bv 32 := 0x02a4bc23.
Lemma F_19b8c : fetch_word Ubsan.M.loaded_segments (0x19b8c : word) = Some W_19b8c.
Proof. vm_refl. Qed.
Lemma D_19b8c : decode_any W_19b8c = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b90 : bv 32 := 0x00040513.
Lemma F_19b90 : fetch_word Ubsan.M.loaded_segments (0x19b90 : word) = Some W_19b90.
Proof. vm_refl. Qed.
Lemma D_19b90 : decode_any W_19b90 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b94 : bv 32 := 0x000ab583.
Lemma F_19b94 : fetch_word Ubsan.M.loaded_segments (0x19b94 : word) = Some W_19b94.
Proof. vm_refl. Qed.
Lemma D_19b94 : decode_any W_19b94 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b98 : bv 32 := 0x02813603.
Lemma F_19b98 : fetch_word Ubsan.M.loaded_segments (0x19b98 : word) = Some W_19b98.
Proof. vm_refl. Qed.
Lemma D_19b98 : decode_any W_19b98 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b9c : bv 32 := 0x0cc59a63.
Lemma F_19b9c : fetch_word Ubsan.M.loaded_segments (0x19b9c : word) = Some W_19b9c.
Proof. vm_refl. Qed.
Lemma D_19b9c : decode_any W_19b9c = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ba0 : bv 32 := 0x06813083.
Lemma F_19ba0 : fetch_word Ubsan.M.loaded_segments (0x19ba0 : word) = Some W_19ba0.
Proof. vm_refl. Qed.
Lemma D_19ba0 : decode_any W_19ba0 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ba4 : bv 32 := 0x06013403.
Lemma F_19ba4 : fetch_word Ubsan.M.loaded_segments (0x19ba4 : word) = Some W_19ba4.
Proof. vm_refl. Qed.
Lemma D_19ba4 : decode_any W_19ba4 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ba8 : bv 32 := 0x05813483.
Lemma F_19ba8 : fetch_word Ubsan.M.loaded_segments (0x19ba8 : word) = Some W_19ba8.
Proof. vm_refl. Qed.
Lemma D_19ba8 : decode_any W_19ba8 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bac : bv 32 := 0x05013903.
Lemma F_19bac : fetch_word Ubsan.M.loaded_segments (0x19bac : word) = Some W_19bac.
Proof. vm_refl. Qed.
Lemma D_19bac : decode_any W_19bac = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bb0 : bv 32 := 0x04813983.
Lemma F_19bb0 : fetch_word Ubsan.M.loaded_segments (0x19bb0 : word) = Some W_19bb0.
Proof. vm_refl. Qed.
Lemma D_19bb0 : decode_any W_19bb0 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bb4 : bv 32 := 0x04013a03.
Lemma F_19bb4 : fetch_word Ubsan.M.loaded_segments (0x19bb4 : word) = Some W_19bb4.
Proof. vm_refl. Qed.
Lemma D_19bb4 : decode_any W_19bb4 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bb8 : bv 32 := 0x03813a83.
Lemma F_19bb8 : fetch_word Ubsan.M.loaded_segments (0x19bb8 : word) = Some W_19bb8.
Proof. vm_refl. Qed.
Lemma D_19bb8 : decode_any W_19bb8 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bbc : bv 32 := 0x03013b03.
Lemma F_19bbc : fetch_word Ubsan.M.loaded_segments (0x19bbc : word) = Some W_19bbc.
Proof. vm_refl. Qed.
Lemma D_19bbc : decode_any W_19bbc = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bc0 : bv 32 := 0x07010113.
Lemma F_19bc0 : fetch_word Ubsan.M.loaded_segments (0x19bc0 : word) = Some W_19bc0.
Proof. vm_refl. Qed.
Lemma D_19bc0 : decode_any W_19bc0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bc4 : bv 32 := 0x00008067.
Lemma F_19bc4 : fetch_word Ubsan.M.loaded_segments (0x19bc4 : word) = Some W_19bc4.
Proof. vm_refl. Qed.
Lemma D_19bc4 : decode_any W_19bc4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bc8 : bv 32 := 0x00800713.
Lemma F_19bc8 : fetch_word Ubsan.M.loaded_segments (0x19bc8 : word) = Some W_19bc8.
Proof. vm_refl. Qed.
Lemma D_19bc8 : decode_any W_19bc8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bcc : bv 32 := 0x000a0593.
Lemma F_19bcc : fetch_word Ubsan.M.loaded_segments (0x19bcc : word) = Some W_19bcc.
Proof. vm_refl. Qed.
Lemma D_19bcc : decode_any W_19bcc = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bd0 : bv 32 := 0x00e98733.
Lemma F_19bd0 : fetch_word Ubsan.M.loaded_segments (0x19bd0 : word) = Some W_19bd0.
Proof. vm_refl. Qed.
Lemma D_19bd0 : decode_any W_19bd0 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bd4 : bv 32 := 0x00073783.
Lemma F_19bd4 : fetch_word Ubsan.M.loaded_segments (0x19bd4 : word) = Some W_19bd4.
Proof. vm_refl. Qed.
Lemma D_19bd4 : decode_any W_19bd4 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bd8 : bv 32 := 0x40ab0b33.
Lemma F_19bd8 : fetch_word Ubsan.M.loaded_segments (0x19bd8 : word) = Some W_19bd8.
Proof. vm_refl. Qed.
Lemma D_19bd8 : decode_any W_19bd8 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bdc : bv 32 := 0x0784a503.
Lemma F_19bdc : fetch_word Ubsan.M.loaded_segments (0x19bdc : word) = Some W_19bdc.
Proof. vm_refl. Qed.
Lemma D_19bdc : decode_any W_19bdc = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_19be0 : bv 32 := 0x40c9093b.
Lemma F_19be0 : fetch_word Ubsan.M.loaded_segments (0x19be0 : word) = Some W_19be0.
Proof. vm_refl. Qed.
Lemma D_19be0 : decode_any W_19be0 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19be4 : bv 32 := 0x40d787b3.
Lemma F_19be4 : fetch_word Ubsan.M.loaded_segments (0x19be4 : word) = Some W_19be4.
Proof. vm_refl. Qed.
Lemma D_19be4 : decode_any W_19be4 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_19be8 : bv 32 := 0x00f73023.
Lemma F_19be8 : fetch_word Ubsan.M.loaded_segments (0x19be8 : word) = Some W_19be8.
Proof. vm_refl. Qed.
Lemma D_19be8 : decode_any W_19be8 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bec : bv 32 := 0x04200893.
Lemma F_19bec : fetch_word Ubsan.M.loaded_segments (0x19bec : word) = Some W_19bec.
Proof. vm_refl. Qed.
Lemma D_19bec : decode_any W_19bec = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bf0 : bv 32 := 0x00090613.
Lemma F_19bf0 : fetch_word Ubsan.M.loaded_segments (0x19bf0 : word) = Some W_19bf0.
Proof. vm_refl. Qed.
Lemma D_19bf0 : decode_any W_19bf0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bf4 : bv 32 := 0x00000073.
Lemma F_19bf4 : fetch_word Ubsan.M.loaded_segments (0x19bf4 : word) = Some W_19bf4.
Proof. vm_refl. Qed.
Lemma D_19bf4 : decode_any W_19bf4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_19bf4 : is_ecall W_19bf4 = true.
Proof. reflexivity. Qed.

Definition W_19bf8 : bv 32 := 0xb25fd0ef.
Lemma F_19bf8 : fetch_word Ubsan.M.loaded_segments (0x19bf8 : word) = Some W_19bf8.
Proof. vm_refl. Qed.
Lemma D_19bf8 : decode_any W_19bf8 = Some (Jal 1 2087716, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bfc : bv 32 := 0x000a0993.
Lemma F_19bfc : fetch_word Ubsan.M.loaded_segments (0x19bfc : word) = Some W_19bfc.
Proof. vm_refl. Qed.
Lemma D_19bfc : decode_any W_19bfc = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c00 : bv 32 := 0xf7650ce3.
Lemma F_19c00 : fetch_word Ubsan.M.loaded_segments (0x19c00 : word) = Some W_19c00.
Proof. vm_refl. Qed.
Lemma D_19c00 : decode_any W_19c00 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c04 : bv 32 := 0x02054c63.
Lemma F_19c04 : fetch_word Ubsan.M.loaded_segments (0x19c04 : word) = Some W_19c04.
Proof. vm_refl. Qed.
Lemma D_19c04 : decode_any W_19c04 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c08 : bv 32 := 0x0089b583.
Lemma F_19c08 : fetch_word Ubsan.M.loaded_segments (0x19c08 : word) = Some W_19c08.
Proof. vm_refl. Qed.
Lemma D_19c08 : decode_any W_19c08 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c0c : bv 32 := 0x00a5b633.
Lemma F_19c0c : fetch_word Ubsan.M.loaded_segments (0x19c0c : word) = Some W_19c0c.
Proof. vm_refl. Qed.
Lemma D_19c0c : decode_any W_19c0c = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c10 : bv 32 := 0x00461a13.
Lemma F_19c10 : fetch_word Ubsan.M.loaded_segments (0x19c10 : word) = Some W_19c10.
Proof. vm_refl. Qed.
Lemma D_19c10 : decode_any W_19c10 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c14 : bv 32 := 0x01498a33.
Lemma F_19c14 : fetch_word Ubsan.M.loaded_segments (0x19c14 : word) = Some W_19c14.
Proof. vm_refl. Qed.
Lemma D_19c14 : decode_any W_19c14 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c18 : bv 32 := 0x000a3703.
Lemma F_19c18 : fetch_word Ubsan.M.loaded_segments (0x19c18 : word) = Some W_19c18.
Proof. vm_refl. Qed.
Lemma D_19c18 : decode_any W_19c18 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c1c : bv 32 := 0x40c006b3.
Lemma F_19c1c : fetch_word Ubsan.M.loaded_segments (0x19c1c : word) = Some W_19c1c.
Proof. vm_refl. Qed.
Lemma D_19c1c : decode_any W_19c1c = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c20 : bv 32 := 0x00b6f6b3.
Lemma F_19c20 : fetch_word Ubsan.M.loaded_segments (0x19c20 : word) = Some W_19c20.
Proof. vm_refl. Qed.
Lemma D_19c20 : decode_any W_19c20 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c24 : bv 32 := 0x40d506b3.
Lemma F_19c24 : fetch_word Ubsan.M.loaded_segments (0x19c24 : word) = Some W_19c24.
Proof. vm_refl. Qed.
Lemma D_19c24 : decode_any W_19c24 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c28 : bv 32 := 0x00d70733.
Lemma F_19c28 : fetch_word Ubsan.M.loaded_segments (0x19c28 : word) = Some W_19c28.
Proof. vm_refl. Qed.
Lemma D_19c28 : decode_any W_19c28 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c2c : bv 32 := 0x00ea3023.
Lemma F_19c2c : fetch_word Ubsan.M.loaded_segments (0x19c2c : word) = Some W_19c2c.
Proof. vm_refl. Qed.
Lemma D_19c2c : decode_any W_19c2c = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c30 : bv 32 := 0xf8a5fce3.
Lemma F_19c30 : fetch_word Ubsan.M.loaded_segments (0x19c30 : word) = Some W_19c30.
Proof. vm_refl. Qed.
Lemma D_19c30 : decode_any W_19c30 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c34 : bv 32 := 0x01800713.
Lemma F_19c34 : fetch_word Ubsan.M.loaded_segments (0x19c34 : word) = Some W_19c34.
Proof. vm_refl. Qed.
Lemma D_19c34 : decode_any W_19c34 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c38 : bv 32 := 0xf95ff06f.
Lemma F_19c38 : fetch_word Ubsan.M.loaded_segments (0x19c38 : word) = Some W_19c38.
Proof. vm_refl. Qed.
Lemma D_19c38 : decode_any W_19c38 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
