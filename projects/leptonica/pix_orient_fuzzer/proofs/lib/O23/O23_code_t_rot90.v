(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6caa4 : bv 32 := 0x00050663.
Lemma F_6caa4 : fetch_word Plain.M.loaded_segments (0x6cafc : word) = Some W_6caa4.
Proof. vm_refl. Qed.
Lemma D_6caa4 : decode_any W_6caa4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caa8 : bv 32 := 0x01052503.
Lemma F_6caa8 : fetch_word Plain.M.loaded_segments (0x6cb00 : word) = Some W_6caa8.
Proof. vm_refl. Qed.
Lemma D_6caa8 : decode_any W_6caa8 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caac : bv 32 := 0x00008067.
Lemma F_6caac : fetch_word Plain.M.loaded_segments (0x6cb04 : word) = Some W_6caac.
Proof. vm_refl. Qed.
Lemma D_6caac : decode_any W_6caac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cda0 : bv 32 := 0x00058463.
Lemma F_6cda0 : fetch_word Plain.M.loaded_segments (0x6cdf8 : word) = Some W_6cda0.
Proof. vm_refl. Qed.
Lemma D_6cda0 : decode_any W_6cda0 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cda4 : bv 32 := 0x0005a023.
Lemma F_6cda4 : fetch_word Plain.M.loaded_segments (0x6cdfc : word) = Some W_6cda4.
Proof. vm_refl. Qed.
Lemma D_6cda4 : decode_any W_6cda4 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cda8 : bv 32 := 0x00060463.
Lemma F_6cda8 : fetch_word Plain.M.loaded_segments (0x6ce00 : word) = Some W_6cda8.
Proof. vm_refl. Qed.
Lemma D_6cda8 : decode_any W_6cda8 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdac : bv 32 := 0x00062023.
Lemma F_6cdac : fetch_word Plain.M.loaded_segments (0x6ce04 : word) = Some W_6cdac.
Proof. vm_refl. Qed.
Lemma D_6cdac : decode_any W_6cdac = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdb0 : bv 32 := 0x00068463.
Lemma F_6cdb0 : fetch_word Plain.M.loaded_segments (0x6ce08 : word) = Some W_6cdb0.
Proof. vm_refl. Qed.
Lemma D_6cdb0 : decode_any W_6cdb0 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdb4 : bv 32 := 0x0006a023.
Lemma F_6cdb4 : fetch_word Plain.M.loaded_segments (0x6ce0c : word) = Some W_6cdb4.
Proof. vm_refl. Qed.
Lemma D_6cdb4 : decode_any W_6cdb4 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdb8 : bv 32 := 0x02050a63.
Lemma F_6cdb8 : fetch_word Plain.M.loaded_segments (0x6ce10 : word) = Some W_6cdb8.
Proof. vm_refl. Qed.
Lemma D_6cdb8 : decode_any W_6cdb8 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdbc : bv 32 := 0x00058663.
Lemma F_6cdbc : fetch_word Plain.M.loaded_segments (0x6ce14 : word) = Some W_6cdbc.
Proof. vm_refl. Qed.
Lemma D_6cdbc : decode_any W_6cdbc = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdc0 : bv 32 := 0x00052703.
Lemma F_6cdc0 : fetch_word Plain.M.loaded_segments (0x6ce18 : word) = Some W_6cdc0.
Proof. vm_refl. Qed.
Lemma D_6cdc0 : decode_any W_6cdc0 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdc4 : bv 32 := 0x00e5a023.
Lemma F_6cdc4 : fetch_word Plain.M.loaded_segments (0x6ce1c : word) = Some W_6cdc4.
Proof. vm_refl. Qed.
Lemma D_6cdc4 : decode_any W_6cdc4 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdc8 : bv 32 := 0x00060663.
Lemma F_6cdc8 : fetch_word Plain.M.loaded_segments (0x6ce20 : word) = Some W_6cdc8.
Proof. vm_refl. Qed.
Lemma D_6cdc8 : decode_any W_6cdc8 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdcc : bv 32 := 0x00452583.
Lemma F_6cdcc : fetch_word Plain.M.loaded_segments (0x6ce24 : word) = Some W_6cdcc.
Proof. vm_refl. Qed.
Lemma D_6cdcc : decode_any W_6cdcc = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdd0 : bv 32 := 0x00b62023.
Lemma F_6cdd0 : fetch_word Plain.M.loaded_segments (0x6ce28 : word) = Some W_6cdd0.
Proof. vm_refl. Qed.
Lemma D_6cdd0 : decode_any W_6cdd0 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdd4 : bv 32 := 0x00000593.
Lemma F_6cdd4 : fetch_word Plain.M.loaded_segments (0x6ce2c : word) = Some W_6cdd4.
Proof. vm_refl. Qed.
Lemma D_6cdd4 : decode_any W_6cdd4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdd8 : bv 32 := 0x00068663.
Lemma F_6cdd8 : fetch_word Plain.M.loaded_segments (0x6ce30 : word) = Some W_6cdd8.
Proof. vm_refl. Qed.
Lemma D_6cdd8 : decode_any W_6cdd8 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cddc : bv 32 := 0x00852503.
Lemma F_6cddc : fetch_word Plain.M.loaded_segments (0x6ce34 : word) = Some W_6cddc.
Proof. vm_refl. Qed.
Lemma D_6cddc : decode_any W_6cddc = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cde0 : bv 32 := 0x00a6a023.
Lemma F_6cde0 : fetch_word Plain.M.loaded_segments (0x6ce38 : word) = Some W_6cde0.
Proof. vm_refl. Qed.
Lemma D_6cde0 : decode_any W_6cde0 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cde4 : bv 32 := 0x00058513.
Lemma F_6cde4 : fetch_word Plain.M.loaded_segments (0x6ce3c : word) = Some W_6cde4.
Proof. vm_refl. Qed.
Lemma D_6cde4 : decode_any W_6cde4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cde8 : bv 32 := 0x00008067.
Lemma F_6cde8 : fetch_word Plain.M.loaded_segments (0x6ce40 : word) = Some W_6cde8.
Proof. vm_refl. Qed.
Lemma D_6cde8 : decode_any W_6cde8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce20 : bv 32 := 0x02050263.
Lemma F_6ce20 : fetch_word Plain.M.loaded_segments (0x6ce78 : word) = Some W_6ce20.
Proof. vm_refl. Qed.
Lemma D_6ce20 : decode_any W_6ce20 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce24 : bv 32 := 0x04058663.
Lemma F_6ce24 : fetch_word Plain.M.loaded_segments (0x6ce7c : word) = Some W_6ce24.
Proof. vm_refl. Qed.
Lemma D_6ce24 : decode_any W_6ce24 = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce28 : bv 32 := 0x0ca58063.
Lemma F_6ce28 : fetch_word Plain.M.loaded_segments (0x6ce80 : word) = Some W_6ce28.
Proof. vm_refl. Qed.
Lemma D_6ce28 : decode_any W_6ce28 = Some (Branch BC_EQ 11 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce2c : bv 32 := 0x00c5a583.
Lemma F_6ce2c : fetch_word Plain.M.loaded_segments (0x6ce84 : word) = Some W_6ce2c.
Proof. vm_refl. Qed.
Lemma D_6ce2c : decode_any W_6ce2c = Some (Load SZ4 true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce30 : bv 32 := 0x06b05a63.
Lemma F_6ce30 : fetch_word Plain.M.loaded_segments (0x6ce88 : word) = Some W_6ce30.
Proof. vm_refl. Qed.
Lemma D_6ce30 : decode_any W_6ce30 = Some (Branch BC_GE 0 11 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce34 : bv 32 := 0x00050613.
Lemma F_6ce34 : fetch_word Plain.M.loaded_segments (0x6ce8c : word) = Some W_6ce34.
Proof. vm_refl. Qed.
Lemma D_6ce34 : decode_any W_6ce34 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce38 : bv 32 := 0x00000513.
Lemma F_6ce38 : fetch_word Plain.M.loaded_segments (0x6ce90 : word) = Some W_6ce38.
Proof. vm_refl. Qed.
Lemma D_6ce38 : decode_any W_6ce38 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce3c : bv 32 := 0x00b62623.
Lemma F_6ce3c : fetch_word Plain.M.loaded_segments (0x6ce94 : word) = Some W_6ce3c.
Proof. vm_refl. Qed.
Lemma D_6ce3c : decode_any W_6ce3c = Some (Store SZ4 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce40 : bv 32 := 0x00008067.
Lemma F_6ce40 : fetch_word Plain.M.loaded_segments (0x6ce98 : word) = Some W_6ce40.
Proof. vm_refl. Qed.
Lemma D_6ce40 : decode_any W_6ce40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cef0 : bv 32 := 0x02058063.
Lemma F_6cef0 : fetch_word Plain.M.loaded_segments (0x6cf48 : word) = Some W_6cef0.
Proof. vm_refl. Qed.
Lemma D_6cef0 : decode_any W_6cef0 = Some (Branch BC_EQ 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cef4 : bv 32 := 0x04050463.
Lemma F_6cef4 : fetch_word Plain.M.loaded_segments (0x6cf4c : word) = Some W_6cef4.
Proof. vm_refl. Qed.
Lemma D_6cef4 : decode_any W_6cef4 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cef8 : bv 32 := 0x06a58c63.
Lemma F_6cef8 : fetch_word Plain.M.loaded_segments (0x6cf50 : word) = Some W_6cef8.
Proof. vm_refl. Qed.
Lemma D_6cef8 : decode_any W_6cef8 = Some (Branch BC_EQ 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cefc : bv 32 := 0x00050613.
Lemma F_6cefc : fetch_word Plain.M.loaded_segments (0x6cf54 : word) = Some W_6cefc.
Proof. vm_refl. Qed.
Lemma D_6cefc : decode_any W_6cefc = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf00 : bv 32 := 0x00000513.
Lemma F_6cf00 : fetch_word Plain.M.loaded_segments (0x6cf58 : word) = Some W_6cf00.
Proof. vm_refl. Qed.
Lemma D_6cf00 : decode_any W_6cf00 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf04 : bv 32 := 0x0185b583.
Lemma F_6cf04 : fetch_word Plain.M.loaded_segments (0x6cf5c : word) = Some W_6cf04.
Proof. vm_refl. Qed.
Lemma D_6cf04 : decode_any W_6cf04 = Some (Load SZ8 true 11 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf08 : bv 32 := 0x00b63c23.
Lemma F_6cf08 : fetch_word Plain.M.loaded_segments (0x6cf60 : word) = Some W_6cf08.
Proof. vm_refl. Qed.
Lemma D_6cf08 : decode_any W_6cf08 = Some (Store SZ8 12 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf0c : bv 32 := 0x00008067.
Lemma F_6cf0c : fetch_word Plain.M.loaded_segments (0x6cf64 : word) = Some W_6cf0c.
Proof. vm_refl. Qed.
Lemma D_6cf0c : decode_any W_6cf0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d1fc : bv 32 := 0x02058063.
Lemma F_6d1fc : fetch_word Plain.M.loaded_segments (0x6d254 : word) = Some W_6d1fc.
Proof. vm_refl. Qed.
Lemma D_6d1fc : decode_any W_6d1fc = Some (Branch BC_EQ 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d200 : bv 32 := 0x04050463.
Lemma F_6d200 : fetch_word Plain.M.loaded_segments (0x6d258 : word) = Some W_6d200.
Proof. vm_refl. Qed.
Lemma D_6d200 : decode_any W_6d200 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d204 : bv 32 := 0x06a58c63.
Lemma F_6d204 : fetch_word Plain.M.loaded_segments (0x6d25c : word) = Some W_6d204.
Proof. vm_refl. Qed.
Lemma D_6d204 : decode_any W_6d204 = Some (Branch BC_EQ 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d208 : bv 32 := 0x00050613.
Lemma F_6d208 : fetch_word Plain.M.loaded_segments (0x6d260 : word) = Some W_6d208.
Proof. vm_refl. Qed.
Lemma D_6d208 : decode_any W_6d208 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d20c : bv 32 := 0x00000513.
Lemma F_6d20c : fetch_word Plain.M.loaded_segments (0x6d264 : word) = Some W_6d20c.
Proof. vm_refl. Qed.
Lemma D_6d20c : decode_any W_6d20c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d210 : bv 32 := 0x0205a583.
Lemma F_6d210 : fetch_word Plain.M.loaded_segments (0x6d268 : word) = Some W_6d210.
Proof. vm_refl. Qed.
Lemma D_6d210 : decode_any W_6d210 = Some (Load SZ4 true 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d214 : bv 32 := 0x02b62023.
Lemma F_6d214 : fetch_word Plain.M.loaded_segments (0x6d26c : word) = Some W_6d214.
Proof. vm_refl. Qed.
Lemma D_6d214 : decode_any W_6d214 = Some (Store SZ4 12 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d218 : bv 32 := 0x00008067.
Lemma F_6d218 : fetch_word Plain.M.loaded_segments (0x6d270 : word) = Some W_6d218.
Proof. vm_refl. Qed.
Lemma D_6d218 : decode_any W_6d218 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d9e8 : bv 32 := 0x00050663.
Lemma F_6d9e8 : fetch_word Plain.M.loaded_segments (0x6da40 : word) = Some W_6d9e8.
Proof. vm_refl. Qed.
Lemma D_6d9e8 : decode_any W_6d9e8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d9ec : bv 32 := 0x03853503.
Lemma F_6d9ec : fetch_word Plain.M.loaded_segments (0x6da44 : word) = Some W_6d9ec.
Proof. vm_refl. Qed.
Lemma D_6d9ec : decode_any W_6d9ec = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d9f0 : bv 32 := 0x00008067.
Lemma F_6d9f0 : fetch_word Plain.M.loaded_segments (0x6da48 : word) = Some W_6d9f0.
Proof. vm_refl. Qed.
Lemma D_6d9f0 : decode_any W_6d9f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877e8 : bv 32 := 0xfb010113.
Lemma F_877e8 : fetch_word Plain.M.loaded_segments (0x87840 : word) = Some W_877e8.
Proof. vm_refl. Qed.
Lemma D_877e8 : decode_any W_877e8 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877ec : bv 32 := 0x04113423.
Lemma F_877ec : fetch_word Plain.M.loaded_segments (0x87844 : word) = Some W_877ec.
Proof. vm_refl. Qed.
Lemma D_877ec : decode_any W_877ec = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877f0 : bv 32 := 0x04813023.
Lemma F_877f0 : fetch_word Plain.M.loaded_segments (0x87848 : word) = Some W_877f0.
Proof. vm_refl. Qed.
Lemma D_877f0 : decode_any W_877f0 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877f4 : bv 32 := 0x02913c23.
Lemma F_877f4 : fetch_word Plain.M.loaded_segments (0x8784c : word) = Some W_877f4.
Proof. vm_refl. Qed.
Lemma D_877f4 : decode_any W_877f4 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877f8 : bv 32 := 0x03213823.
Lemma F_877f8 : fetch_word Plain.M.loaded_segments (0x87850 : word) = Some W_877f8.
Proof. vm_refl. Qed.
Lemma D_877f8 : decode_any W_877f8 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877fc : bv 32 := 0x03313423.
Lemma F_877fc : fetch_word Plain.M.loaded_segments (0x87854 : word) = Some W_877fc.
Proof. vm_refl. Qed.
Lemma D_877fc : decode_any W_877fc = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87800 : bv 32 := 0x03413023.
Lemma F_87800 : fetch_word Plain.M.loaded_segments (0x87858 : word) = Some W_87800.
Proof. vm_refl. Qed.
Lemma D_87800 : decode_any W_87800 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87804 : bv 32 := 0x01513c23.
Lemma F_87804 : fetch_word Plain.M.loaded_segments (0x8785c : word) = Some W_87804.
Proof. vm_refl. Qed.
Lemma D_87804 : decode_any W_87804 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87808 : bv 32 := 0x12050e63.
Lemma F_87808 : fetch_word Plain.M.loaded_segments (0x87860 : word) = Some W_87808.
Proof. vm_refl. Qed.
Lemma D_87808 : decode_any W_87808 = Some (Branch BC_EQ 10 0 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8780c : bv 32 := 0x00058993.
Lemma F_8780c : fetch_word Plain.M.loaded_segments (0x87864 : word) = Some W_8780c.
Proof. vm_refl. Qed.
Lemma D_8780c : decode_any W_8780c = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87810 : bv 32 := 0x01010593.
Lemma F_87810 : fetch_word Plain.M.loaded_segments (0x87868 : word) = Some W_87810.
Proof. vm_refl. Qed.
Lemma D_87810 : decode_any W_87810 = Some (OpImm ALU_ADD 11 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87814 : bv 32 := 0x01410613.
Lemma F_87814 : fetch_word Plain.M.loaded_segments (0x8786c : word) = Some W_87814.
Proof. vm_refl. Qed.
Lemma D_87814 : decode_any W_87814 = Some (OpImm ALU_ADD 12 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87818 : bv 32 := 0x00c10693.
Lemma F_87818 : fetch_word Plain.M.loaded_segments (0x87870 : word) = Some W_87818.
Proof. vm_refl. Qed.
Lemma D_87818 : decode_any W_87818 = Some (OpImm ALU_ADD 13 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8781c : bv 32 := 0x00050413.
Lemma F_8781c : fetch_word Plain.M.loaded_segments (0x87874 : word) = Some W_8781c.
Proof. vm_refl. Qed.
Lemma D_8781c : decode_any W_8781c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87820 : bv 32 := 0xd80e50ef.
Lemma F_87820 : fetch_word Plain.M.loaded_segments (0x87878 : word) = Some W_87820.
Proof. vm_refl. Qed.
Lemma D_87820 : decode_any W_87820 = Some (Jal 1 1987968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87824 : bv 32 := 0x00c12603.
Lemma F_87824 : fetch_word Plain.M.loaded_segments (0x8787c : word) = Some W_87824.
Proof. vm_refl. Qed.
Lemma D_87824 : decode_any W_87824 = Some (Load SZ4 true 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87828 : bv 32 := 0x02000513.
Lemma F_87828 : fetch_word Plain.M.loaded_segments (0x87880 : word) = Some W_87828.
Proof. vm_refl. Qed.
Lemma D_87828 : decode_any W_87828 = Some (OpImm ALU_ADD 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8782c : bv 32 := 0x40c56663.
Lemma F_8782c : fetch_word Plain.M.loaded_segments (0x87884 : word) = Some W_8782c.
Proof. vm_refl. Qed.
Lemma D_8782c : decode_any W_8782c = Some (Branch BC_LTU 10 12 1036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87830 : bv 32 := 0x10001537.
Lemma F_87830 : fetch_word Plain.M.loaded_segments (0x87888 : word) = Some W_87830.
Proof. vm_refl. Qed.
Lemma D_87830 : decode_any W_87830 = Some (Lui 10 65537, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87834 : bv 32 := 0x00451513.
Lemma F_87834 : fetch_word Plain.M.loaded_segments (0x8788c : word) = Some W_87834.
Proof. vm_refl. Qed.
Lemma D_87834 : decode_any W_87834 = Some (ShiftImm ALU_SLL 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87838 : bv 32 := 0x11650513.
Lemma F_87838 : fetch_word Plain.M.loaded_segments (0x87890 : word) = Some W_87838.
Proof. vm_refl. Qed.
Lemma D_87838 : decode_any W_87838 = Some (OpImm ALU_ADD 10 10 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8783c : bv 32 := 0x00c55533.
Lemma F_8783c : fetch_word Plain.M.loaded_segments (0x87894 : word) = Some W_8783c.
Proof. vm_refl. Qed.
Lemma D_8783c : decode_any W_8783c = Some (Op ALU_SRL 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87840 : bv 32 := 0x00157513.
Lemma F_87840 : fetch_word Plain.M.loaded_segments (0x87898 : word) = Some W_87840.
Proof. vm_refl. Qed.
Lemma D_87840 : decode_any W_87840 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87844 : bv 32 := 0x3e050a63.
Lemma F_87844 : fetch_word Plain.M.loaded_segments (0x8789c : word) = Some W_87844.
Proof. vm_refl. Qed.
Lemma D_87844 : decode_any W_87844 = Some (Branch BC_EQ 10 0 1012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87848 : bv 32 := 0xfff00513.
Lemma F_87848 : fetch_word Plain.M.loaded_segments (0x878a0 : word) = Some W_87848.
Proof. vm_refl. Qed.
Lemma D_87848 : decode_any W_87848 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8784c : bv 32 := 0x00a98663.
Lemma F_8784c : fetch_word Plain.M.loaded_segments (0x878a4 : word) = Some W_8784c.
Proof. vm_refl. Qed.
Lemma D_8784c : decode_any W_8784c = Some (Branch BC_EQ 19 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87850 : bv 32 := 0x00100513.
Lemma F_87850 : fetch_word Plain.M.loaded_segments (0x878a8 : word) = Some W_87850.
Proof. vm_refl. Qed.
Lemma D_87850 : decode_any W_87850 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87854 : bv 32 := 0x22a99263.
Lemma F_87854 : fetch_word Plain.M.loaded_segments (0x878ac : word) = Some W_87854.
Proof. vm_refl. Qed.
Lemma D_87854 : decode_any W_87854 = Some (Branch BC_NE 19 10 548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87858 : bv 32 := 0x01412503.
Lemma F_87858 : fetch_word Plain.M.loaded_segments (0x878b0 : word) = Some W_87858.
Proof. vm_refl. Qed.
Lemma D_87858 : decode_any W_87858 = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8785c : bv 32 := 0x01012583.
Lemma F_8785c : fetch_word Plain.M.loaded_segments (0x878b4 : word) = Some W_8785c.
Proof. vm_refl. Qed.
Lemma D_8785c : decode_any W_8785c = Some (Load SZ4 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87860 : bv 32 := 0xd81e40ef.
Lemma F_87860 : fetch_word Plain.M.loaded_segments (0x878b8 : word) = Some W_87860.
Proof. vm_refl. Qed.
Lemma D_87860 : decode_any W_87860 = Some (Jal 1 1985920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87864 : bv 32 := 0x00a13023.
Lemma F_87864 : fetch_word Plain.M.loaded_segments (0x878bc : word) = Some W_87864.
Proof. vm_refl. Qed.
Lemma D_87864 : decode_any W_87864 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87868 : bv 32 := 0x22050c63.
Lemma F_87868 : fetch_word Plain.M.loaded_segments (0x878c0 : word) = Some W_87868.
Proof. vm_refl. Qed.
Lemma D_87868 : decode_any W_87868 = Some (Branch BC_EQ 10 0 568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8786c : bv 32 := 0x00040593.
Lemma F_8786c : fetch_word Plain.M.loaded_segments (0x878c4 : word) = Some W_8786c.
Proof. vm_refl. Qed.
Lemma D_8786c : decode_any W_8786c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87870 : bv 32 := 0xf08e50ef.
Lemma F_87870 : fetch_word Plain.M.loaded_segments (0x878c8 : word) = Some W_87870.
Proof. vm_refl. Qed.
Lemma D_87870 : decode_any W_87870 = Some (Jal 1 1988360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87874 : bv 32 := 0x00013503.
Lemma F_87874 : fetch_word Plain.M.loaded_segments (0x878cc : word) = Some W_87874.
Proof. vm_refl. Qed.
Lemma D_87874 : decode_any W_87874 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87878 : bv 32 := 0x00040593.
Lemma F_87878 : fetch_word Plain.M.loaded_segments (0x878d0 : word) = Some W_87878.
Proof. vm_refl. Qed.
Lemma D_87878 : decode_any W_87878 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8787c : bv 32 := 0xe74e50ef.
Lemma F_8787c : fetch_word Plain.M.loaded_segments (0x878d4 : word) = Some W_8787c.
Proof. vm_refl. Qed.
Lemma D_8787c : decode_any W_8787c = Some (Jal 1 1988212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87880 : bv 32 := 0x00013503.
Lemma F_87880 : fetch_word Plain.M.loaded_segments (0x878d8 : word) = Some W_87880.
Proof. vm_refl. Qed.
Lemma D_87880 : decode_any W_87880 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87884 : bv 32 := 0x00040593.
Lemma F_87884 : fetch_word Plain.M.loaded_segments (0x878dc : word) = Some W_87884.
Proof. vm_refl. Qed.
Lemma D_87884 : decode_any W_87884 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87888 : bv 32 := 0x975e50ef.
Lemma F_87888 : fetch_word Plain.M.loaded_segments (0x878e0 : word) = Some W_87888.
Proof. vm_refl. Qed.
Lemma D_87888 : decode_any W_87888 = Some (Jal 1 1988980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8788c : bv 32 := 0x00013503.
Lemma F_8788c : fetch_word Plain.M.loaded_segments (0x878e4 : word) = Some W_8788c.
Proof. vm_refl. Qed.
Lemma D_8788c : decode_any W_8788c = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87890 : bv 32 := 0x00040593.
Lemma F_87890 : fetch_word Plain.M.loaded_segments (0x878e8 : word) = Some W_87890.
Proof. vm_refl. Qed.
Lemma D_87890 : decode_any W_87890 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87894 : bv 32 := 0xd8ce50ef.
Lemma F_87894 : fetch_word Plain.M.loaded_segments (0x878ec : word) = Some W_87894.
Proof. vm_refl. Qed.
Lemma D_87894 : decode_any W_87894 = Some (Jal 1 1987980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87898 : bv 32 := 0x00040513.
Lemma F_87898 : fetch_word Plain.M.loaded_segments (0x878f0 : word) = Some W_87898.
Proof. vm_refl. Qed.
Lemma D_87898 : decode_any W_87898 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8789c : bv 32 := 0x94ce60ef.
Lemma F_8789c : fetch_word Plain.M.loaded_segments (0x878f4 : word) = Some W_8789c.
Proof. vm_refl. Qed.
Lemma D_8789c : decode_any W_8789c = Some (Jal 1 1990988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878a0 : bv 32 := 0x00050493.
Lemma F_878a0 : fetch_word Plain.M.loaded_segments (0x878f8 : word) = Some W_878a0.
Proof. vm_refl. Qed.
Lemma D_878a0 : decode_any W_878a0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878a4 : bv 32 := 0x00040513.
Lemma F_878a4 : fetch_word Plain.M.loaded_segments (0x878fc : word) = Some W_878a4.
Proof. vm_refl. Qed.
Lemma D_878a4 : decode_any W_878a4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878a8 : bv 32 := 0x9fce50ef.
Lemma F_878a8 : fetch_word Plain.M.loaded_segments (0x87900 : word) = Some W_878a8.
Proof. vm_refl. Qed.
Lemma D_878a8 : decode_any W_878a8 = Some (Jal 1 1987068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878ac : bv 32 := 0x00013583.
Lemma F_878ac : fetch_word Plain.M.loaded_segments (0x87904 : word) = Some W_878ac.
Proof. vm_refl. Qed.
Lemma D_878ac : decode_any W_878ac = Some (Load SZ8 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878b0 : bv 32 := 0x00050913.
Lemma F_878b0 : fetch_word Plain.M.loaded_segments (0x87908 : word) = Some W_878b0.
Proof. vm_refl. Qed.
Lemma D_878b0 : decode_any W_878b0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878b4 : bv 32 := 0x00058513.
Lemma F_878b4 : fetch_word Plain.M.loaded_segments (0x8790c : word) = Some W_878b4.
Proof. vm_refl. Qed.
Lemma D_878b4 : decode_any W_878b4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878b8 : bv 32 := 0x930e60ef.
Lemma F_878b8 : fetch_word Plain.M.loaded_segments (0x87910 : word) = Some W_878b8.
Proof. vm_refl. Qed.
Lemma D_878b8 : decode_any W_878b8 = Some (Jal 1 1990960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878bc : bv 32 := 0x00013583.
Lemma F_878bc : fetch_word Plain.M.loaded_segments (0x87914 : word) = Some W_878bc.
Proof. vm_refl. Qed.
Lemma D_878bc : decode_any W_878bc = Some (Load SZ8 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878c0 : bv 32 := 0x00050413.
Lemma F_878c0 : fetch_word Plain.M.loaded_segments (0x87918 : word) = Some W_878c0.
Proof. vm_refl. Qed.
Lemma D_878c0 : decode_any W_878c0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878c4 : bv 32 := 0x00058513.
Lemma F_878c4 : fetch_word Plain.M.loaded_segments (0x8791c : word) = Some W_878c4.
Proof. vm_refl. Qed.
Lemma D_878c4 : decode_any W_878c4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878c8 : bv 32 := 0x9dce50ef.
Lemma F_878c8 : fetch_word Plain.M.loaded_segments (0x87920 : word) = Some W_878c8.
Proof. vm_refl. Qed.
Lemma D_878c8 : decode_any W_878c8 = Some (Jal 1 1987036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878cc : bv 32 := 0x00c12583.
Lemma F_878cc : fetch_word Plain.M.loaded_segments (0x87924 : word) = Some W_878cc.
Proof. vm_refl. Qed.
Lemma D_878cc : decode_any W_878cc = Some (Load SZ4 true 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878d0 : bv 32 := 0xfff58593.
Lemma F_878d0 : fetch_word Plain.M.loaded_segments (0x87928 : word) = Some W_878d0.
Proof. vm_refl. Qed.
Lemma D_878d0 : decode_any W_878d0 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878d4 : bv 32 := 0x00100613.
Lemma F_878d4 : fetch_word Plain.M.loaded_segments (0x8792c : word) = Some W_878d4.
Proof. vm_refl. Qed.
Lemma D_878d4 : decode_any W_878d4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878d8 : bv 32 := 0x1ec99863.
Lemma F_878d8 : fetch_word Plain.M.loaded_segments (0x87930 : word) = Some W_878d8.
Proof. vm_refl. Qed.
Lemma D_878d8 : decode_any W_878d8 = Some (Branch BC_NE 19 12 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878dc : bv 32 := 0x01f00613.
Lemma F_878dc : fetch_word Plain.M.loaded_segments (0x87934 : word) = Some W_878dc.
Proof. vm_refl. Qed.
Lemma D_878dc : decode_any W_878dc = Some (OpImm ALU_ADD 12 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878e0 : bv 32 := 0x5eb66e63.
Lemma F_878e0 : fetch_word Plain.M.loaded_segments (0x87938 : word) = Some W_878e0.
Proof. vm_refl. Qed.
Lemma D_878e0 : decode_any W_878e0 = Some (Branch BC_LTU 12 11 1532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878e4 : bv 32 := 0x00259593.
Lemma F_878e4 : fetch_word Plain.M.loaded_segments (0x8793c : word) = Some W_878e4.
Proof. vm_refl. Qed.
Lemma D_878e4 : decode_any W_878e4 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878e8 : bv 32 := 0xfff98617.
Lemma F_878e8 : fetch_word Plain.M.loaded_segments (0x87940 : word) = Some W_878e8.
Proof. vm_refl. Qed.
Lemma D_878e8 : decode_any W_878e8 = Some (Auipc 12 1048472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878ec : bv 32 := 0xd8860613.
Lemma F_878ec : fetch_word Plain.M.loaded_segments (0x87944 : word) = Some W_878ec.
Proof. vm_refl. Qed.
Lemma D_878ec : decode_any W_878ec = Some (OpImm ALU_ADD 12 12 3464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878f0 : bv 32 := 0x00c585b3.
Lemma F_878f0 : fetch_word Plain.M.loaded_segments (0x87948 : word) = Some W_878f0.
Proof. vm_refl. Qed.
Lemma D_878f0 : decode_any W_878f0 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878f4 : bv 32 := 0x0005a583.
Lemma F_878f4 : fetch_word Plain.M.loaded_segments (0x8794c : word) = Some W_878f4.
Proof. vm_refl. Qed.
Lemma D_878f4 : decode_any W_878f4 = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878f8 : bv 32 := 0x00c585b3.
Lemma F_878f8 : fetch_word Plain.M.loaded_segments (0x87950 : word) = Some W_878f8.
Proof. vm_refl. Qed.
Lemma D_878f8 : decode_any W_878f8 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_878fc : bv 32 := 0x00058067.
Lemma F_878fc : fetch_word Plain.M.loaded_segments (0x87954 : word) = Some W_878fc.
Proof. vm_refl. Qed.
Lemma D_878fc : decode_any W_878fc = Some (Jalr 0 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87900 : bv 32 := 0x01412303.
Lemma F_87900 : fetch_word Plain.M.loaded_segments (0x87958 : word) = Some W_87900.
Proof. vm_refl. Qed.
Lemma D_87900 : decode_any W_87900 = Some (Load SZ4 true 6 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87904 : bv 32 := 0x1a6052e3.
Lemma F_87904 : fetch_word Plain.M.loaded_segments (0x8795c : word) = Some W_87904.
Proof. vm_refl. Qed.
Lemma D_87904 : decode_any W_87904 = Some (Branch BC_GE 0 6 2468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87908 : bv 32 := 0x00000593.
Lemma F_87908 : fetch_word Plain.M.loaded_segments (0x87960 : word) = Some W_87908.
Proof. vm_refl. Qed.
Lemma D_87908 : decode_any W_87908 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8790c : bv 32 := 0x00000613.
Lemma F_8790c : fetch_word Plain.M.loaded_segments (0x87964 : word) = Some W_8790c.
Proof. vm_refl. Qed.
Lemma D_8790c : decode_any W_8790c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87910 : bv 32 := 0x01012683.
Lemma F_87910 : fetch_word Plain.M.loaded_segments (0x87968 : word) = Some W_87910.
Proof. vm_refl. Qed.
Lemma D_87910 : decode_any W_87910 = Some (Load SZ4 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87914 : bv 32 := 0x00551293.
Lemma F_87914 : fetch_word Plain.M.loaded_segments (0x8796c : word) = Some W_87914.
Proof. vm_refl. Qed.
Lemma D_87914 : decode_any W_87914 = Some (ShiftImm ALU_SLL 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87918 : bv 32 := 0x00251513.
Lemma F_87918 : fetch_word Plain.M.loaded_segments (0x87970 : word) = Some W_87918.
Proof. vm_refl. Qed.
Lemma D_87918 : decode_any W_87918 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8791c : bv 32 := 0x02000713.
Lemma F_8791c : fetch_word Plain.M.loaded_segments (0x87974 : word) = Some W_8791c.
Proof. vm_refl. Qed.
Lemma D_8791c : decode_any W_8791c = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87920 : bv 32 := 0x800007b7.
Lemma F_87920 : fetch_word Plain.M.loaded_segments (0x87978 : word) = Some W_87920.
Proof. vm_refl. Qed.
Lemma D_87920 : decode_any W_87920 = Some (Lui 15 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87924 : bv 32 := 0x00169813.
Lemma F_87924 : fetch_word Plain.M.loaded_segments (0x8797c : word) = Some W_87924.
Proof. vm_refl. Qed.
Lemma D_87924 : decode_any W_87924 = Some (ShiftImm ALU_SLL 16 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87928 : bv 32 := 0x03b85813.
Lemma F_87928 : fetch_word Plain.M.loaded_segments (0x87980 : word) = Some W_87928.
Proof. vm_refl. Qed.
Lemma D_87928 : decode_any W_87928 = Some (ShiftImm ALU_SRL 16 16 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8792c : bv 32 := 0x010688bb.
Lemma F_8792c : fetch_word Plain.M.loaded_segments (0x87984 : word) = Some W_8792c.
Proof. vm_refl. Qed.
Lemma D_8792c : decode_any W_8792c = Some (Op32 ALU_ADD 17 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87930 : bv 32 := 0x4058d81b.
Lemma F_87930 : fetch_word Plain.M.loaded_segments (0x87988 : word) = Some W_87930.
Proof. vm_refl. Qed.
Lemma D_87930 : decode_any W_87930 = Some (ShiftImm32 ALU_SRA 16 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87934 : bv 32 := 0xfe08f893.
Lemma F_87934 : fetch_word Plain.M.loaded_segments (0x8798c : word) = Some W_87934.
Proof. vm_refl. Qed.
Lemma D_87934 : decode_any W_87934 = Some (OpImm ALU_AND 17 17 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87938 : bv 32 := 0x00229293.
Lemma F_87938 : fetch_word Plain.M.loaded_segments (0x87990 : word) = Some W_87938.
Proof. vm_refl. Qed.
Lemma D_87938 : decode_any W_87938 = Some (ShiftImm ALU_SLL 5 5 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8793c : bv 32 := 0x00068393.
Lemma F_8793c : fetch_word Plain.M.loaded_segments (0x87994 : word) = Some W_8793c.
Proof. vm_refl. Qed.
Lemma D_8793c : decode_any W_8793c = Some (OpImm ALU_ADD 7 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87940 : bv 32 := 0x0600006f.
Lemma F_87940 : fetch_word Plain.M.loaded_segments (0x87998 : word) = Some W_87940.
Proof. vm_refl. Qed.
Lemma D_87940 : decode_any W_87940 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87990 : bv 32 := 0x01412303.
Lemma F_87990 : fetch_word Plain.M.loaded_segments (0x879e8 : word) = Some W_87990.
Proof. vm_refl. Qed.
Lemma D_87990 : decode_any W_87990 = Some (Load SZ4 true 6 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87994 : bv 32 := 0x0016061b.
Lemma F_87994 : fetch_word Plain.M.loaded_segments (0x879ec : word) = Some W_87994.
Proof. vm_refl. Qed.
Lemma D_87994 : decode_any W_87994 = Some (OpImm32 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87998 : bv 32 := 0x00158593.
Lemma F_87998 : fetch_word Plain.M.loaded_segments (0x879f0 : word) = Some W_87998.
Proof. vm_refl. Qed.
Lemma D_87998 : decode_any W_87998 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8799c : bv 32 := 0x106656e3.
Lemma F_8799c : fetch_word Plain.M.loaded_segments (0x879f4 : word) = Some W_8799c.
Proof. vm_refl. Qed.
Lemma D_8799c : decode_any W_8799c = Some (Branch BC_GE 12 6 2316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879a0 : bv 32 := 0x0035de13.
Lemma F_879a0 : fetch_word Plain.M.loaded_segments (0x879f8 : word) = Some W_879a0.
Proof. vm_refl. Qed.
Lemma D_879a0 : decode_any W_879a0 = Some (ShiftImm ALU_SRL 28 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879a4 : bv 32 := 0xfff64e93.
Lemma F_879a4 : fetch_word Plain.M.loaded_segments (0x879fc : word) = Some W_879a4.
Proof. vm_refl. Qed.
Lemma D_879a4 : decode_any W_879a4 = Some (OpImm ALU_XOR 29 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879a8 : bv 32 := 0xffce7e13.
Lemma F_879a8 : fetch_word Plain.M.loaded_segments (0x87a00 : word) = Some W_879a8.
Proof. vm_refl. Qed.
Lemma D_879a8 : decode_any W_879a8 = Some (OpImm ALU_AND 28 28 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879ac : bv 32 := 0x01d3033b.
Lemma F_879ac : fetch_word Plain.M.loaded_segments (0x87a04 : word) = Some W_879ac.
Proof. vm_refl. Qed.
Lemma D_879ac : decode_any W_879ac = Some (Op32 ALU_ADD 6 6 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879b0 : bv 32 := 0x03230333.
Lemma F_879b0 : fetch_word Plain.M.loaded_segments (0x87a08 : word) = Some W_879b0.
Proof. vm_refl. Qed.
Lemma D_879b0 : decode_any W_879b0 = Some (Mul M_MUL 6 6 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879b4 : bv 32 := 0x00231313.
Lemma F_879b4 : fetch_word Plain.M.loaded_segments (0x87a0c : word) = Some W_879b4.
Proof. vm_refl. Qed.
Lemma D_879b4 : decode_any W_879b4 = Some (ShiftImm ALU_SLL 6 6 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879b8 : bv 32 := 0x00648333.
Lemma F_879b8 : fetch_word Plain.M.loaded_segments (0x87a10 : word) = Some W_879b8.
Proof. vm_refl. Qed.
Lemma D_879b8 : decode_any W_879b8 = Some (Op ALU_ADD 6 9 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879bc : bv 32 := 0x00040e93.
Lemma F_879bc : fetch_word Plain.M.loaded_segments (0x87a14 : word) = Some W_879bc.
Proof. vm_refl. Qed.
Lemma D_879bc : decode_any W_879bc = Some (OpImm ALU_ADD 29 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879c0 : bv 32 := 0x06e6c263.
Lemma F_879c0 : fetch_word Plain.M.loaded_segments (0x87a18 : word) = Some W_879c0.
Proof. vm_refl. Qed.
Lemma D_879c0 : decode_any W_879c0 = Some (Branch BC_LT 13 14 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879c4 : bv 32 := 0x00000393.
Lemma F_879c4 : fetch_word Plain.M.loaded_segments (0x87a1c : word) = Some W_879c4.
Proof. vm_refl. Qed.
Lemma D_879c4 : decode_any W_879c4 = Some (OpImm ALU_ADD 7 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879c8 : bv 32 := 0x00c7df3b.
Lemma F_879c8 : fetch_word Plain.M.loaded_segments (0x87a20 : word) = Some W_879c8.
Proof. vm_refl. Qed.
Lemma D_879c8 : decode_any W_879c8 = Some (Op32 ALU_SRL 30 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879cc : bv 32 := 0x00040e93.
Lemma F_879cc : fetch_word Plain.M.loaded_segments (0x87a24 : word) = Some W_879cc.
Proof. vm_refl. Qed.
Lemma D_879cc : decode_any W_879cc = Some (OpImm ALU_ADD 29 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879d0 : bv 32 := 0x0100006f.
Lemma F_879d0 : fetch_word Plain.M.loaded_segments (0x87a28 : word) = Some W_879d0.
Proof. vm_refl. Qed.
Lemma D_879d0 : decode_any W_879d0 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879d4 : bv 32 := 0x005e8eb3.
Lemma F_879d4 : fetch_word Plain.M.loaded_segments (0x87a2c : word) = Some W_879d4.
Proof. vm_refl. Qed.
Lemma D_879d4 : decode_any W_879d4 = Some (Op ALU_ADD 29 29 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879d8 : bv 32 := 0x00138393.
Lemma F_879d8 : fetch_word Plain.M.loaded_segments (0x87a30 : word) = Some W_879d8.
Proof. vm_refl. Qed.
Lemma D_879d8 : decode_any W_879d8 = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879dc : bv 32 := 0x05038263.
Lemma F_879dc : fetch_word Plain.M.loaded_segments (0x87a34 : word) = Some W_879dc.
Proof. vm_refl. Qed.
Lemma D_879dc : decode_any W_879dc = Some (Branch BC_EQ 7 16 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879e0 : bv 32 := 0x00239f93.
Lemma F_879e0 : fetch_word Plain.M.loaded_segments (0x87a38 : word) = Some W_879e0.
Proof. vm_refl. Qed.
Lemma D_879e0 : decode_any W_879e0 = Some (ShiftImm ALU_SLL 31 7 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879e4 : bv 32 := 0x01f30fb3.
Lemma F_879e4 : fetch_word Plain.M.loaded_segments (0x87a3c : word) = Some W_879e4.
Proof. vm_refl. Qed.
Lemma D_879e4 : decode_any W_879e4 = Some (Op ALU_ADD 31 6 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879e8 : bv 32 := 0x000faf83.
Lemma F_879e8 : fetch_word Plain.M.loaded_segments (0x87a40 : word) = Some W_879e8.
Proof. vm_refl. Qed.
Lemma D_879e8 : decode_any W_879e8 = Some (Load SZ4 true 31 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879ec : bv 32 := 0xfe0f84e3.
Lemma F_879ec : fetch_word Plain.M.loaded_segments (0x87a44 : word) = Some W_879ec.
Proof. vm_refl. Qed.
Lemma D_879ec : decode_any W_879ec = Some (Branch BC_EQ 31 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879f0 : bv 32 := 0x00000993.
Lemma F_879f0 : fetch_word Plain.M.loaded_segments (0x87a48 : word) = Some W_879f0.
Proof. vm_refl. Qed.
Lemma D_879f0 : decode_any W_879f0 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879f4 : bv 32 := 0x0100006f.
Lemma F_879f4 : fetch_word Plain.M.loaded_segments (0x87a4c : word) = Some W_879f4.
Proof. vm_refl. Qed.
Lemma D_879f4 : decode_any W_879f4 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879f8 : bv 32 := 0x0019899b.
Lemma F_879f8 : fetch_word Plain.M.loaded_segments (0x87a50 : word) = Some W_879f8.
Proof. vm_refl. Qed.
Lemma D_879f8 : decode_any W_879f8 = Some (OpImm32 19 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879fc : bv 32 := 0x00ae8eb3.
Lemma F_879fc : fetch_word Plain.M.loaded_segments (0x87a54 : word) = Some W_879fc.
Proof. vm_refl. Qed.
Lemma D_879fc : decode_any W_879fc = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a00 : bv 32 := 0xfce98ce3.
Lemma F_87a00 : fetch_word Plain.M.loaded_segments (0x87a58 : word) = Some W_87a00.
Proof. vm_refl. Qed.
Lemma D_87a00 : decode_any W_87a00 = Some (Branch BC_EQ 19 14 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a04 : bv 32 := 0x013f9a3b.
Lemma F_87a04 : fetch_word Plain.M.loaded_segments (0x87a5c : word) = Some W_87a04.
Proof. vm_refl. Qed.
Lemma D_87a04 : decode_any W_87a04 = Some (Op32 ALU_SLL 20 31 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a08 : bv 32 := 0xfe0a58e3.
Lemma F_87a08 : fetch_word Plain.M.loaded_segments (0x87a60 : word) = Some W_87a08.
Proof. vm_refl. Qed.
Lemma D_87a08 : decode_any W_87a08 = Some (Branch BC_GE 20 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a0c : bv 32 := 0x01ce8a33.
Lemma F_87a0c : fetch_word Plain.M.loaded_segments (0x87a64 : word) = Some W_87a0c.
Proof. vm_refl. Qed.
Lemma D_87a0c : decode_any W_87a0c = Some (Op ALU_ADD 20 29 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a10 : bv 32 := 0x000a2a83.
Lemma F_87a10 : fetch_word Plain.M.loaded_segments (0x87a68 : word) = Some W_87a10.
Proof. vm_refl. Qed.
Lemma D_87a10 : decode_any W_87a10 = Some (Load SZ4 true 21 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a14 : bv 32 := 0x01eaeab3.
Lemma F_87a14 : fetch_word Plain.M.loaded_segments (0x87a6c : word) = Some W_87a14.
Proof. vm_refl. Qed.
Lemma D_87a14 : decode_any W_87a14 = Some (Op ALU_OR 21 21 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a18 : bv 32 := 0x015a2023.
Lemma F_87a18 : fetch_word Plain.M.loaded_segments (0x87a70 : word) = Some W_87a18.
Proof. vm_refl. Qed.
Lemma D_87a18 : decode_any W_87a18 = Some (Store SZ4 20 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a1c : bv 32 := 0xfddff06f.
Lemma F_87a1c : fetch_word Plain.M.loaded_segments (0x87a74 : word) = Some W_87a1c.
Proof. vm_refl. Qed.
Lemma D_87a1c : decode_any W_87a1c = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a20 : bv 32 := 0x01012383.
Lemma F_87a20 : fetch_word Plain.M.loaded_segments (0x87a78 : word) = Some W_87a20.
Proof. vm_refl. Qed.
Lemma D_87a20 : decode_any W_87a20 = Some (Load SZ4 true 7 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a24 : bv 32 := 0xf678d6e3.
Lemma F_87a24 : fetch_word Plain.M.loaded_segments (0x87a7c : word) = Some W_87a24.
Proof. vm_refl. Qed.
Lemma D_87a24 : decode_any W_87a24 = Some (Branch BC_GE 17 7 8044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a28 : bv 32 := 0x00c7df3b.
Lemma F_87a28 : fetch_word Plain.M.loaded_segments (0x87a80 : word) = Some W_87a28.
Proof. vm_refl. Qed.
Lemma D_87a28 : decode_any W_87a28 = Some (Op32 ALU_SRL 30 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a2c : bv 32 := 0x01ce8e33.
Lemma F_87a2c : fetch_word Plain.M.loaded_segments (0x87a84 : word) = Some W_87a2c.
Proof. vm_refl. Qed.
Lemma D_87a2c : decode_any W_87a2c = Some (Op ALU_ADD 28 29 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a30 : bv 32 := 0x00088e93.
Lemma F_87a30 : fetch_word Plain.M.loaded_segments (0x87a88 : word) = Some W_87a30.
Proof. vm_refl. Qed.
Lemma D_87a30 : decode_any W_87a30 = Some (OpImm ALU_ADD 29 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a34 : bv 32 := 0x0100006f.
Lemma F_87a34 : fetch_word Plain.M.loaded_segments (0x87a8c : word) = Some W_87a34.
Proof. vm_refl. Qed.
Lemma D_87a34 : decode_any W_87a34 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a38 : bv 32 := 0x001e8e9b.
Lemma F_87a38 : fetch_word Plain.M.loaded_segments (0x87a90 : word) = Some W_87a38.
Proof. vm_refl. Qed.
Lemma D_87a38 : decode_any W_87a38 = Some (OpImm32 29 29 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a3c : bv 32 := 0x00ae0e33.
Lemma F_87a3c : fetch_word Plain.M.loaded_segments (0x87a94 : word) = Some W_87a3c.
Proof. vm_refl. Qed.
Lemma D_87a3c : decode_any W_87a3c = Some (Op ALU_ADD 28 28 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a40 : bv 32 := 0xf47ed8e3.
Lemma F_87a40 : fetch_word Plain.M.loaded_segments (0x87a98 : word) = Some W_87a40.
Proof. vm_refl. Qed.
Lemma D_87a40 : decode_any W_87a40 = Some (Branch BC_GE 29 7 8016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a44 : bv 32 := 0x405edf9b.
Lemma F_87a44 : fetch_word Plain.M.loaded_segments (0x87a9c : word) = Some W_87a44.
Proof. vm_refl. Qed.
Lemma D_87a44 : decode_any W_87a44 = Some (ShiftImm32 ALU_SRA 31 29 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a48 : bv 32 := 0x002f9f93.
Lemma F_87a48 : fetch_word Plain.M.loaded_segments (0x87aa0 : word) = Some W_87a48.
Proof. vm_refl. Qed.
Lemma D_87a48 : decode_any W_87a48 = Some (ShiftImm ALU_SLL 31 31 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a4c : bv 32 := 0x01f30fb3.
Lemma F_87a4c : fetch_word Plain.M.loaded_segments (0x87aa4 : word) = Some W_87a4c.
Proof. vm_refl. Qed.
Lemma D_87a4c : decode_any W_87a4c = Some (Op ALU_ADD 31 6 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a50 : bv 32 := 0x000faf83.
Lemma F_87a50 : fetch_word Plain.M.loaded_segments (0x87aa8 : word) = Some W_87a50.
Proof. vm_refl. Qed.
Lemma D_87a50 : decode_any W_87a50 = Some (Load SZ4 true 31 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a54 : bv 32 := 0xfffec993.
Lemma F_87a54 : fetch_word Plain.M.loaded_segments (0x87aac : word) = Some W_87a54.
Proof. vm_refl. Qed.
Lemma D_87a54 : decode_any W_87a54 = Some (OpImm ALU_XOR 19 29 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a58 : bv 32 := 0x013fdfbb.
Lemma F_87a58 : fetch_word Plain.M.loaded_segments (0x87ab0 : word) = Some W_87a58.
Proof. vm_refl. Qed.
Lemma D_87a58 : decode_any W_87a58 = Some (Op32 ALU_SRL 31 31 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a5c : bv 32 := 0x001fff93.
Lemma F_87a5c : fetch_word Plain.M.loaded_segments (0x87ab4 : word) = Some W_87a5c.
Proof. vm_refl. Qed.
Lemma D_87a5c : decode_any W_87a5c = Some (OpImm ALU_AND 31 31 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a60 : bv 32 := 0xfc0f8ce3.
Lemma F_87a60 : fetch_word Plain.M.loaded_segments (0x87ab8 : word) = Some W_87a60.
Proof. vm_refl. Qed.
Lemma D_87a60 : decode_any W_87a60 = Some (Branch BC_EQ 31 0 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a64 : bv 32 := 0x000e2383.
Lemma F_87a64 : fetch_word Plain.M.loaded_segments (0x87abc : word) = Some W_87a64.
Proof. vm_refl. Qed.
Lemma D_87a64 : decode_any W_87a64 = Some (Load SZ4 true 7 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a68 : bv 32 := 0x01e3e3b3.
Lemma F_87a68 : fetch_word Plain.M.loaded_segments (0x87ac0 : word) = Some W_87a68.
Proof. vm_refl. Qed.
Lemma D_87a68 : decode_any W_87a68 = Some (Op ALU_OR 7 7 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a6c : bv 32 := 0x007e2023.
Lemma F_87a6c : fetch_word Plain.M.loaded_segments (0x87ac4 : word) = Some W_87a6c.
Proof. vm_refl. Qed.
Lemma D_87a6c : decode_any W_87a6c = Some (Store SZ4 28 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a70 : bv 32 := 0x01012383.
Lemma F_87a70 : fetch_word Plain.M.loaded_segments (0x87ac8 : word) = Some W_87a70.
Proof. vm_refl. Qed.
Lemma D_87a70 : decode_any W_87a70 = Some (Load SZ4 true 7 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a74 : bv 32 := 0xfc5ff06f.
Lemma F_87a74 : fetch_word Plain.M.loaded_segments (0x87acc : word) = Some W_87a74.
Proof. vm_refl. Qed.
Lemma D_87a74 : decode_any W_87a74 = Some (Jal 0 2097092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87aa0 : bv 32 := 0x0008b517.
Lemma F_87aa0 : fetch_word Plain.M.loaded_segments (0x87af8 : word) = Some W_87aa0.
Proof. vm_refl. Qed.
Lemma D_87aa0 : decode_any W_87aa0 = Some (Auipc 10 139, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87aa4 : bv 32 := 0xad053503.
Lemma F_87aa4 : fetch_word Plain.M.loaded_segments (0x87afc : word) = Some W_87aa4.
Proof. vm_refl. Qed.
Lemma D_87aa4 : decode_any W_87aa4 = Some (Load SZ8 true 10 10 2768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87aa8 : bv 32 := 0x00052503.
Lemma F_87aa8 : fetch_word Plain.M.loaded_segments (0x87b00 : word) = Some W_87aa8.
Proof. vm_refl. Qed.
Lemma D_87aa8 : decode_any W_87aa8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87aac : bv 32 := 0x00500593.
Lemma F_87aac : fetch_word Plain.M.loaded_segments (0x87b04 : word) = Some W_87aac.
Proof. vm_refl. Qed.
Lemma D_87aac : decode_any W_87aac = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ab0 : bv 32 := 0x1aa5cc63.
Lemma F_87ab0 : fetch_word Plain.M.loaded_segments (0x87b08 : word) = Some W_87ab0.
Proof. vm_refl. Qed.
Lemma D_87ab0 : decode_any W_87ab0 = Some (Branch BC_LT 11 10 440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ab4 : bv 32 := 0xfff8b517.
Lemma F_87ab4 : fetch_word Plain.M.loaded_segments (0x87b0c : word) = Some W_87ab4.
Proof. vm_refl. Qed.
Lemma D_87ab4 : decode_any W_87ab4 = Some (Auipc 10 1048459, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ab8 : bv 32 := 0xfff92597.
Lemma F_87ab8 : fetch_word Plain.M.loaded_segments (0x87b10 : word) = Some W_87ab8.
Proof. vm_refl. Qed.
Lemma D_87ab8 : decode_any W_87ab8 = Some (Auipc 11 1048466, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87abc : bv 32 := 0xbce50513.
Lemma F_87abc : fetch_word Plain.M.loaded_segments (0x87b14 : word) = Some W_87abc.
Proof. vm_refl. Qed.
Lemma D_87abc : decode_any W_87abc = Some (OpImm ALU_ADD 10 10 3022, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ac0 : bv 32 := 0x8b158593.
Lemma F_87ac0 : fetch_word Plain.M.loaded_segments (0x87b18 : word) = Some W_87ac0.
Proof. vm_refl. Qed.
Lemma D_87ac0 : decode_any W_87ac0 = Some (OpImm ALU_ADD 11 11 2225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ac4 : bv 32 := 0x1980006f.
Lemma F_87ac4 : fetch_word Plain.M.loaded_segments (0x87b1c : word) = Some W_87ac4.
Proof. vm_refl. Qed.
Lemma D_87ac4 : decode_any W_87ac4 = Some (Jal 0 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ac8 : bv 32 := 0x01f00613.
Lemma F_87ac8 : fetch_word Plain.M.loaded_segments (0x87b20 : word) = Some W_87ac8.
Proof. vm_refl. Qed.
Lemma D_87ac8 : decode_any W_87ac8 = Some (OpImm ALU_ADD 12 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87acc : bv 32 := 0x42b66863.
Lemma F_87acc : fetch_word Plain.M.loaded_segments (0x87b24 : word) = Some W_87acc.
Proof. vm_refl. Qed.
Lemma D_87acc : decode_any W_87acc = Some (Branch BC_LTU 12 11 1072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ad0 : bv 32 := 0x00259593.
Lemma F_87ad0 : fetch_word Plain.M.loaded_segments (0x87b28 : word) = Some W_87ad0.
Proof. vm_refl. Qed.
Lemma D_87ad0 : decode_any W_87ad0 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ad4 : bv 32 := 0xfff98617.
Lemma F_87ad4 : fetch_word Plain.M.loaded_segments (0x87b2c : word) = Some W_87ad4.
Proof. vm_refl. Qed.
Lemma D_87ad4 : decode_any W_87ad4 = Some (Auipc 12 1048472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ad8 : bv 32 := 0xb1c60613.
Lemma F_87ad8 : fetch_word Plain.M.loaded_segments (0x87b30 : word) = Some W_87ad8.
Proof. vm_refl. Qed.
Lemma D_87ad8 : decode_any W_87ad8 = Some (OpImm ALU_ADD 12 12 2844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87adc : bv 32 := 0x00c585b3.
Lemma F_87adc : fetch_word Plain.M.loaded_segments (0x87b34 : word) = Some W_87adc.
Proof. vm_refl. Qed.
Lemma D_87adc : decode_any W_87adc = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ae0 : bv 32 := 0x0005a583.
Lemma F_87ae0 : fetch_word Plain.M.loaded_segments (0x87b38 : word) = Some W_87ae0.
Proof. vm_refl. Qed.
Lemma D_87ae0 : decode_any W_87ae0 = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ae4 : bv 32 := 0x00c585b3.
Lemma F_87ae4 : fetch_word Plain.M.loaded_segments (0x87b3c : word) = Some W_87ae4.
Proof. vm_refl. Qed.
Lemma D_87ae4 : decode_any W_87ae4 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ae8 : bv 32 := 0x00058067.
Lemma F_87ae8 : fetch_word Plain.M.loaded_segments (0x87b40 : word) = Some W_87ae8.
Proof. vm_refl. Qed.
Lemma D_87ae8 : decode_any W_87ae8 = Some (Jalr 0 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87aec : bv 32 := 0x01412383.
Lemma F_87aec : fetch_word Plain.M.loaded_segments (0x87b44 : word) = Some W_87aec.
Proof. vm_refl. Qed.
Lemma D_87aec : decode_any W_87aec = Some (Load SZ4 true 7 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87af0 : bv 32 := 0x7a705c63.
Lemma F_87af0 : fetch_word Plain.M.loaded_segments (0x87b48 : word) = Some W_87af0.
Proof. vm_refl. Qed.
Lemma D_87af0 : decode_any W_87af0 = Some (Branch BC_GE 0 7 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87af4 : bv 32 := 0x00000593.
Lemma F_87af4 : fetch_word Plain.M.loaded_segments (0x87b4c : word) = Some W_87af4.
Proof. vm_refl. Qed.
Lemma D_87af4 : decode_any W_87af4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87af8 : bv 32 := 0x01012603.
Lemma F_87af8 : fetch_word Plain.M.loaded_segments (0x87b50 : word) = Some W_87af8.
Proof. vm_refl. Qed.
Lemma D_87af8 : decode_any W_87af8 = Some (Load SZ4 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87afc : bv 32 := 0x0055171b.
Lemma F_87afc : fetch_word Plain.M.loaded_segments (0x87b54 : word) = Some W_87afc.
Proof. vm_refl. Qed.
Lemma D_87afc : decode_any W_87afc = Some (ShiftImm32 ALU_SLL 14 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b00 : bv 32 := 0x00251793.
Lemma F_87b00 : fetch_word Plain.M.loaded_segments (0x87b58 : word) = Some W_87b00.
Proof. vm_refl. Qed.
Lemma D_87b00 : decode_any W_87b00 = Some (ShiftImm ALU_SLL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b04 : bv 32 := 0x02000693.
Lemma F_87b04 : fetch_word Plain.M.loaded_segments (0x87b5c : word) = Some W_87b04.
Proof. vm_refl. Qed.
Lemma D_87b04 : decode_any W_87b04 = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b08 : bv 32 := 0x40e00833.
Lemma F_87b08 : fetch_word Plain.M.loaded_segments (0x87b60 : word) = Some W_87b08.
Proof. vm_refl. Qed.
Lemma D_87b08 : decode_any W_87b08 = Some (Op ALU_SUB 16 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b0c : bv 32 := 0x40f00733.
Lemma F_87b0c : fetch_word Plain.M.loaded_segments (0x87b64 : word) = Some W_87b0c.
Proof. vm_refl. Qed.
Lemma D_87b0c : decode_any W_87b0c = Some (Op ALU_SUB 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b10 : bv 32 := 0x00281793.
Lemma F_87b10 : fetch_word Plain.M.loaded_segments (0x87b68 : word) = Some W_87b10.
Proof. vm_refl. Qed.
Lemma D_87b10 : decode_any W_87b10 = Some (ShiftImm ALU_SLL 15 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b14 : bv 32 := 0x00161813.
Lemma F_87b14 : fetch_word Plain.M.loaded_segments (0x87b6c : word) = Some W_87b14.
Proof. vm_refl. Qed.
Lemma D_87b14 : decode_any W_87b14 = Some (ShiftImm ALU_SLL 16 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b18 : bv 32 := 0x03b85813.
Lemma F_87b18 : fetch_word Plain.M.loaded_segments (0x87b70 : word) = Some W_87b18.
Proof. vm_refl. Qed.
Lemma D_87b18 : decode_any W_87b18 = Some (ShiftImm ALU_SRL 16 16 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b1c : bv 32 := 0x010608bb.
Lemma F_87b1c : fetch_word Plain.M.loaded_segments (0x87b74 : word) = Some W_87b1c.
Proof. vm_refl. Qed.
Lemma D_87b1c : decode_any W_87b1c = Some (Op32 ALU_ADD 17 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b20 : bv 32 := 0x4058d81b.
Lemma F_87b20 : fetch_word Plain.M.loaded_segments (0x87b78 : word) = Some W_87b20.
Proof. vm_refl. Qed.
Lemma D_87b20 : decode_any W_87b20 = Some (ShiftImm32 ALU_SRA 16 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b24 : bv 32 := 0xfe08f893.
Lemma F_87b24 : fetch_word Plain.M.loaded_segments (0x87b7c : word) = Some W_87b24.
Proof. vm_refl. Qed.
Lemma D_87b24 : decode_any W_87b24 = Some (OpImm ALU_AND 17 17 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b28 : bv 32 := 0x800002b7.
Lemma F_87b28 : fetch_word Plain.M.loaded_segments (0x87b80 : word) = Some W_87b28.
Proof. vm_refl. Qed.
Lemma D_87b28 : decode_any W_87b28 = Some (Lui 5 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b2c : bv 32 := 0x00060e93.
Lemma F_87b2c : fetch_word Plain.M.loaded_segments (0x87b84 : word) = Some W_87b2c.
Proof. vm_refl. Qed.
Lemma D_87b2c : decode_any W_87b2c = Some (OpImm ALU_ADD 29 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b30 : bv 32 := 0x0100006f.
Lemma F_87b30 : fetch_word Plain.M.loaded_segments (0x87b88 : word) = Some W_87b30.
Proof. vm_refl. Qed.
Lemma D_87b30 : decode_any W_87b30 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b34 : bv 32 := 0x01412383.
Lemma F_87b34 : fetch_word Plain.M.loaded_segments (0x87b8c : word) = Some W_87b34.
Proof. vm_refl. Qed.
Lemma D_87b34 : decode_any W_87b34 = Some (Load SZ4 true 7 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b38 : bv 32 := 0x0015859b.
Lemma F_87b38 : fetch_word Plain.M.loaded_segments (0x87b90 : word) = Some W_87b38.
Proof. vm_refl. Qed.
Lemma D_87b38 : decode_any W_87b38 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b3c : bv 32 := 0x7675d663.
Lemma F_87b3c : fetch_word Plain.M.loaded_segments (0x87b94 : word) = Some W_87b3c.
Proof. vm_refl. Qed.
Lemma D_87b3c : decode_any W_87b3c = Some (Branch BC_GE 11 7 1900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b40 : bv 32 := 0xfffe8e13.
Lemma F_87b40 : fetch_word Plain.M.loaded_segments (0x87b98 : word) = Some W_87b40.
Proof. vm_refl. Qed.
Lemma D_87b40 : decode_any W_87b40 = Some (OpImm ALU_ADD 28 29 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b44 : bv 32 := 0xfff5c313.
Lemma F_87b44 : fetch_word Plain.M.loaded_segments (0x87b9c : word) = Some W_87b44.
Proof. vm_refl. Qed.
Lemma D_87b44 : decode_any W_87b44 = Some (OpImm ALU_XOR 6 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b48 : bv 32 := 0x02ae0e33.
Lemma F_87b48 : fetch_word Plain.M.loaded_segments (0x87ba0 : word) = Some W_87b48.
Proof. vm_refl. Qed.
Lemma D_87b48 : decode_any W_87b48 = Some (Mul M_MUL 28 28 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b4c : bv 32 := 0x006383bb.
Lemma F_87b4c : fetch_word Plain.M.loaded_segments (0x87ba4 : word) = Some W_87b4c.
Proof. vm_refl. Qed.
Lemma D_87b4c : decode_any W_87b4c = Some (Op32 ALU_ADD 7 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b50 : bv 32 := 0x002e1e13.
Lemma F_87b50 : fetch_word Plain.M.loaded_segments (0x87ba8 : word) = Some W_87b50.
Proof. vm_refl. Qed.
Lemma D_87b50 : decode_any W_87b50 = Some (ShiftImm ALU_SLL 28 28 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b54 : bv 32 := 0x03238f33.
Lemma F_87b54 : fetch_word Plain.M.loaded_segments (0x87bac : word) = Some W_87b54.
Proof. vm_refl. Qed.
Lemma D_87b54 : decode_any W_87b54 = Some (Mul M_MUL 30 7 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b58 : bv 32 := 0x01c403b3.
Lemma F_87b58 : fetch_word Plain.M.loaded_segments (0x87bb0 : word) = Some W_87b58.
Proof. vm_refl. Qed.
Lemma D_87b58 : decode_any W_87b58 = Some (Op ALU_ADD 7 8 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b5c : bv 32 := 0x002f1e13.
Lemma F_87b5c : fetch_word Plain.M.loaded_segments (0x87bb4 : word) = Some W_87b5c.
Proof. vm_refl. Qed.
Lemma D_87b5c : decode_any W_87b5c = Some (ShiftImm ALU_SLL 28 30 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b60 : bv 32 := 0x01c48e33.
Lemma F_87b60 : fetch_word Plain.M.loaded_segments (0x87bb8 : word) = Some W_87b60.
Proof. vm_refl. Qed.
Lemma D_87b60 : decode_any W_87b60 = Some (Op ALU_ADD 28 9 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b64 : bv 32 := 0x06d64863.
Lemma F_87b64 : fetch_word Plain.M.loaded_segments (0x87bbc : word) = Some W_87b64.
Proof. vm_refl. Qed.
Lemma D_87b64 : decode_any W_87b64 = Some (Branch BC_LT 12 13 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b68 : bv 32 := 0x00000e93.
Lemma F_87b68 : fetch_word Plain.M.loaded_segments (0x87bc0 : word) = Some W_87b68.
Proof. vm_refl. Qed.
Lemma D_87b68 : decode_any W_87b68 = Some (OpImm ALU_ADD 29 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b6c : bv 32 := 0x0100006f.
Lemma F_87b6c : fetch_word Plain.M.loaded_segments (0x87bc4 : word) = Some W_87b6c.
Proof. vm_refl. Qed.
Lemma D_87b6c : decode_any W_87b6c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b70 : bv 32 := 0x00f383b3.
Lemma F_87b70 : fetch_word Plain.M.loaded_segments (0x87bc8 : word) = Some W_87b70.
Proof. vm_refl. Qed.
Lemma D_87b70 : decode_any W_87b70 = Some (Op ALU_ADD 7 7 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b74 : bv 32 := 0x001e8e93.
Lemma F_87b74 : fetch_word Plain.M.loaded_segments (0x87bcc : word) = Some W_87b74.
Proof. vm_refl. Qed.
Lemma D_87b74 : decode_any W_87b74 = Some (OpImm ALU_ADD 29 29 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b78 : bv 32 := 0x050e8c63.
Lemma F_87b78 : fetch_word Plain.M.loaded_segments (0x87bd0 : word) = Some W_87b78.
Proof. vm_refl. Qed.
Lemma D_87b78 : decode_any W_87b78 = Some (Branch BC_EQ 29 16 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b7c : bv 32 := 0x002e9f13.
Lemma F_87b7c : fetch_word Plain.M.loaded_segments (0x87bd4 : word) = Some W_87b7c.
Proof. vm_refl. Qed.
Lemma D_87b7c : decode_any W_87b7c = Some (ShiftImm ALU_SLL 30 29 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b80 : bv 32 := 0x01ee0f33.
Lemma F_87b80 : fetch_word Plain.M.loaded_segments (0x87bd8 : word) = Some W_87b80.
Proof. vm_refl. Qed.
Lemma D_87b80 : decode_any W_87b80 = Some (Op ALU_ADD 30 28 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b84 : bv 32 := 0x000f2f03.
Lemma F_87b84 : fetch_word Plain.M.loaded_segments (0x87bdc : word) = Some W_87b84.
Proof. vm_refl. Qed.
Lemma D_87b84 : decode_any W_87b84 = Some (Load SZ4 true 30 30 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b88 : bv 32 := 0xfe0f04e3.
Lemma F_87b88 : fetch_word Plain.M.loaded_segments (0x87be0 : word) = Some W_87b88.
Proof. vm_refl. Qed.
Lemma D_87b88 : decode_any W_87b88 = Some (Branch BC_EQ 30 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b8c : bv 32 := 0x00000f93.
Lemma F_87b8c : fetch_word Plain.M.loaded_segments (0x87be4 : word) = Some W_87b8c.
Proof. vm_refl. Qed.
Lemma D_87b8c : decode_any W_87b8c = Some (OpImm ALU_ADD 31 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b90 : bv 32 := 0x0100006f.
Lemma F_87b90 : fetch_word Plain.M.loaded_segments (0x87be8 : word) = Some W_87b90.
Proof. vm_refl. Qed.
Lemma D_87b90 : decode_any W_87b90 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b94 : bv 32 := 0x001f8f9b.
Lemma F_87b94 : fetch_word Plain.M.loaded_segments (0x87bec : word) = Some W_87b94.
Proof. vm_refl. Qed.
Lemma D_87b94 : decode_any W_87b94 = Some (OpImm32 31 31 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b98 : bv 32 := 0x00e383b3.
Lemma F_87b98 : fetch_word Plain.M.loaded_segments (0x87bf0 : word) = Some W_87b98.
Proof. vm_refl. Qed.
Lemma D_87b98 : decode_any W_87b98 = Some (Op ALU_ADD 7 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b9c : bv 32 := 0xfcdf8ce3.
Lemma F_87b9c : fetch_word Plain.M.loaded_segments (0x87bf4 : word) = Some W_87b9c.
Proof. vm_refl. Qed.
Lemma D_87b9c : decode_any W_87b9c = Some (Branch BC_EQ 31 13 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ba0 : bv 32 := 0x01ff19bb.
Lemma F_87ba0 : fetch_word Plain.M.loaded_segments (0x87bf8 : word) = Some W_87ba0.
Proof. vm_refl. Qed.
Lemma D_87ba0 : decode_any W_87ba0 = Some (Op32 ALU_SLL 19 30 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ba4 : bv 32 := 0xfe09d8e3.
Lemma F_87ba4 : fetch_word Plain.M.loaded_segments (0x87bfc : word) = Some W_87ba4.
Proof. vm_refl. Qed.
Lemma D_87ba4 : decode_any W_87ba4 = Some (Branch BC_GE 19 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ba8 : bv 32 := 0x01412983.
Lemma F_87ba8 : fetch_word Plain.M.loaded_segments (0x87c00 : word) = Some W_87ba8.
Proof. vm_refl. Qed.
Lemma D_87ba8 : decode_any W_87ba8 = Some (Load SZ4 true 19 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bac : bv 32 := 0x006989b3.
Lemma F_87bac : fetch_word Plain.M.loaded_segments (0x87c04 : word) = Some W_87bac.
Proof. vm_refl. Qed.
Lemma D_87bac : decode_any W_87bac = Some (Op ALU_ADD 19 19 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bb0 : bv 32 := 0x4059da1b.
Lemma F_87bb0 : fetch_word Plain.M.loaded_segments (0x87c08 : word) = Some W_87bb0.
Proof. vm_refl. Qed.
Lemma D_87bb0 : decode_any W_87bb0 = Some (ShiftImm32 ALU_SRA 20 19 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bb4 : bv 32 := 0x002a1a13.
Lemma F_87bb4 : fetch_word Plain.M.loaded_segments (0x87c0c : word) = Some W_87bb4.
Proof. vm_refl. Qed.
Lemma D_87bb4 : decode_any W_87bb4 = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bb8 : bv 32 := 0x01438a33.
Lemma F_87bb8 : fetch_word Plain.M.loaded_segments (0x87c10 : word) = Some W_87bb8.
Proof. vm_refl. Qed.
Lemma D_87bb8 : decode_any W_87bb8 = Some (Op ALU_ADD 20 7 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bbc : bv 32 := 0x000a2a83.
Lemma F_87bbc : fetch_word Plain.M.loaded_segments (0x87c14 : word) = Some W_87bbc.
Proof. vm_refl. Qed.
Lemma D_87bbc : decode_any W_87bbc = Some (Load SZ4 true 21 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bc0 : bv 32 := 0x0132d9bb.
Lemma F_87bc0 : fetch_word Plain.M.loaded_segments (0x87c18 : word) = Some W_87bc0.
Proof. vm_refl. Qed.
Lemma D_87bc0 : decode_any W_87bc0 = Some (Op32 ALU_SRL 19 5 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bc4 : bv 32 := 0x0159e9b3.
Lemma F_87bc4 : fetch_word Plain.M.loaded_segments (0x87c1c : word) = Some W_87bc4.
Proof. vm_refl. Qed.
Lemma D_87bc4 : decode_any W_87bc4 = Some (Op ALU_OR 19 19 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bc8 : bv 32 := 0x013a2023.
Lemma F_87bc8 : fetch_word Plain.M.loaded_segments (0x87c20 : word) = Some W_87bc8.
Proof. vm_refl. Qed.
Lemma D_87bc8 : decode_any W_87bc8 = Some (Store SZ4 20 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bcc : bv 32 := 0xfc9ff06f.
Lemma F_87bcc : fetch_word Plain.M.loaded_segments (0x87c24 : word) = Some W_87bcc.
Proof. vm_refl. Qed.
Lemma D_87bcc : decode_any W_87bcc = Some (Jal 0 2097096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bd0 : bv 32 := 0x01012e83.
Lemma F_87bd0 : fetch_word Plain.M.loaded_segments (0x87c28 : word) = Some W_87bd0.
Proof. vm_refl. Qed.
Lemma D_87bd0 : decode_any W_87bd0 = Some (Load SZ4 true 29 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bd4 : bv 32 := 0xf7d8d0e3.
Lemma F_87bd4 : fetch_word Plain.M.loaded_segments (0x87c2c : word) = Some W_87bd4.
Proof. vm_refl. Qed.
Lemma D_87bd4 : decode_any W_87bd4 = Some (Branch BC_GE 17 29 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bd8 : bv 32 := 0x00088f13.
Lemma F_87bd8 : fetch_word Plain.M.loaded_segments (0x87c30 : word) = Some W_87bd8.
Proof. vm_refl. Qed.
Lemma D_87bd8 : decode_any W_87bd8 = Some (OpImm ALU_ADD 30 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bdc : bv 32 := 0x0100006f.
Lemma F_87bdc : fetch_word Plain.M.loaded_segments (0x87c34 : word) = Some W_87bdc.
Proof. vm_refl. Qed.
Lemma D_87bdc : decode_any W_87bdc = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87be0 : bv 32 := 0x001f0f1b.
Lemma F_87be0 : fetch_word Plain.M.loaded_segments (0x87c38 : word) = Some W_87be0.
Proof. vm_refl. Qed.
Lemma D_87be0 : decode_any W_87be0 = Some (OpImm32 30 30 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87be4 : bv 32 := 0x00e383b3.
Lemma F_87be4 : fetch_word Plain.M.loaded_segments (0x87c3c : word) = Some W_87be4.
Proof. vm_refl. Qed.
Lemma D_87be4 : decode_any W_87be4 = Some (Op ALU_ADD 7 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87be8 : bv 32 := 0xf5df56e3.
Lemma F_87be8 : fetch_word Plain.M.loaded_segments (0x87c40 : word) = Some W_87be8.
Proof. vm_refl. Qed.
Lemma D_87be8 : decode_any W_87be8 = Some (Branch BC_GE 30 29 8012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bec : bv 32 := 0x405f5f9b.
Lemma F_87bec : fetch_word Plain.M.loaded_segments (0x87c44 : word) = Some W_87bec.
Proof. vm_refl. Qed.
Lemma D_87bec : decode_any W_87bec = Some (ShiftImm32 ALU_SRA 31 30 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bf0 : bv 32 := 0x002f9f93.
Lemma F_87bf0 : fetch_word Plain.M.loaded_segments (0x87c48 : word) = Some W_87bf0.
Proof. vm_refl. Qed.
Lemma D_87bf0 : decode_any W_87bf0 = Some (ShiftImm ALU_SLL 31 31 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bf4 : bv 32 := 0x01fe0fb3.
Lemma F_87bf4 : fetch_word Plain.M.loaded_segments (0x87c4c : word) = Some W_87bf4.
Proof. vm_refl. Qed.
Lemma D_87bf4 : decode_any W_87bf4 = Some (Op ALU_ADD 31 28 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bf8 : bv 32 := 0x000faf83.
Lemma F_87bf8 : fetch_word Plain.M.loaded_segments (0x87c50 : word) = Some W_87bf8.
Proof. vm_refl. Qed.
Lemma D_87bf8 : decode_any W_87bf8 = Some (Load SZ4 true 31 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bfc : bv 32 := 0xffff4993.
Lemma F_87bfc : fetch_word Plain.M.loaded_segments (0x87c54 : word) = Some W_87bfc.
Proof. vm_refl. Qed.
Lemma D_87bfc : decode_any W_87bfc = Some (OpImm ALU_XOR 19 30 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c00 : bv 32 := 0x013fdfbb.
Lemma F_87c00 : fetch_word Plain.M.loaded_segments (0x87c58 : word) = Some W_87c00.
Proof. vm_refl. Qed.
Lemma D_87c00 : decode_any W_87c00 = Some (Op32 ALU_SRL 31 31 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c04 : bv 32 := 0x001fff93.
Lemma F_87c04 : fetch_word Plain.M.loaded_segments (0x87c5c : word) = Some W_87c04.
Proof. vm_refl. Qed.
Lemma D_87c04 : decode_any W_87c04 = Some (OpImm ALU_AND 31 31 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c08 : bv 32 := 0xfc0f8ce3.
Lemma F_87c08 : fetch_word Plain.M.loaded_segments (0x87c60 : word) = Some W_87c08.
Proof. vm_refl. Qed.
Lemma D_87c08 : decode_any W_87c08 = Some (Branch BC_EQ 31 0 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c0c : bv 32 := 0x01412e83.
Lemma F_87c0c : fetch_word Plain.M.loaded_segments (0x87c64 : word) = Some W_87c0c.
Proof. vm_refl. Qed.
Lemma D_87c0c : decode_any W_87c0c = Some (Load SZ4 true 29 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c10 : bv 32 := 0x006e8eb3.
Lemma F_87c10 : fetch_word Plain.M.loaded_segments (0x87c68 : word) = Some W_87c10.
Proof. vm_refl. Qed.
Lemma D_87c10 : decode_any W_87c10 = Some (Op ALU_ADD 29 29 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c14 : bv 32 := 0x405edf9b.
Lemma F_87c14 : fetch_word Plain.M.loaded_segments (0x87c6c : word) = Some W_87c14.
Proof. vm_refl. Qed.
Lemma D_87c14 : decode_any W_87c14 = Some (ShiftImm32 ALU_SRA 31 29 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c18 : bv 32 := 0x002f9f93.
Lemma F_87c18 : fetch_word Plain.M.loaded_segments (0x87c70 : word) = Some W_87c18.
Proof. vm_refl. Qed.
Lemma D_87c18 : decode_any W_87c18 = Some (ShiftImm ALU_SLL 31 31 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c1c : bv 32 := 0x01f38fb3.
Lemma F_87c1c : fetch_word Plain.M.loaded_segments (0x87c74 : word) = Some W_87c1c.
Proof. vm_refl. Qed.
Lemma D_87c1c : decode_any W_87c1c = Some (Op ALU_ADD 31 7 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c20 : bv 32 := 0x000fa983.
Lemma F_87c20 : fetch_word Plain.M.loaded_segments (0x87c78 : word) = Some W_87c20.
Proof. vm_refl. Qed.
Lemma D_87c20 : decode_any W_87c20 = Some (Load SZ4 true 19 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c24 : bv 32 := 0x01d2debb.
Lemma F_87c24 : fetch_word Plain.M.loaded_segments (0x87c7c : word) = Some W_87c24.
Proof. vm_refl. Qed.
Lemma D_87c24 : decode_any W_87c24 = Some (Op32 ALU_SRL 29 5 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c28 : bv 32 := 0x013eeeb3.
Lemma F_87c28 : fetch_word Plain.M.loaded_segments (0x87c80 : word) = Some W_87c28.
Proof. vm_refl. Qed.
Lemma D_87c28 : decode_any W_87c28 = Some (Op ALU_OR 29 29 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c2c : bv 32 := 0x01dfa023.
Lemma F_87c2c : fetch_word Plain.M.loaded_segments (0x87c84 : word) = Some W_87c2c.
Proof. vm_refl. Qed.
Lemma D_87c2c : decode_any W_87c2c = Some (Store SZ4 31 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c30 : bv 32 := 0x01012e83.
Lemma F_87c30 : fetch_word Plain.M.loaded_segments (0x87c88 : word) = Some W_87c30.
Proof. vm_refl. Qed.
Lemma D_87c30 : decode_any W_87c30 = Some (Load SZ4 true 29 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c34 : bv 32 := 0xfadff06f.
Lemma F_87c34 : fetch_word Plain.M.loaded_segments (0x87c8c : word) = Some W_87c34.
Proof. vm_refl. Qed.
Lemma D_87c34 : decode_any W_87c34 = Some (Jal 0 2097068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c5c : bv 32 := 0x00000613.
Lemma F_87c5c : fetch_word Plain.M.loaded_segments (0x87cb4 : word) = Some W_87c5c.
Proof. vm_refl. Qed.
Lemma D_87c5c : decode_any W_87c5c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c60 : bv 32 := 0xc64db0ef.
Lemma F_87c60 : fetch_word Plain.M.loaded_segments (0x87cb8 : word) = Some W_87c60.
Proof. vm_refl. Qed.
Lemma D_87c60 : decode_any W_87c60 = Some (Jal 1 1946724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87c64 : bv 32 := 0x6480006f.
Lemma F_87c64 : fetch_word Plain.M.loaded_segments (0x87cbc : word) = Some W_87c64.
Proof. vm_refl. Qed.
Lemma D_87c64 : decode_any W_87c64 = Some (Jal 0 1608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882a8 : bv 32 := 0x00013503.
Lemma F_882a8 : fetch_word Plain.M.loaded_segments (0x88300 : word) = Some W_882a8.
Proof. vm_refl. Qed.
Lemma D_882a8 : decode_any W_882a8 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882ac : bv 32 := 0x04813083.
Lemma F_882ac : fetch_word Plain.M.loaded_segments (0x88304 : word) = Some W_882ac.
Proof. vm_refl. Qed.
Lemma D_882ac : decode_any W_882ac = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882b0 : bv 32 := 0x04013403.
Lemma F_882b0 : fetch_word Plain.M.loaded_segments (0x88308 : word) = Some W_882b0.
Proof. vm_refl. Qed.
Lemma D_882b0 : decode_any W_882b0 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882b4 : bv 32 := 0x03813483.
Lemma F_882b4 : fetch_word Plain.M.loaded_segments (0x8830c : word) = Some W_882b4.
Proof. vm_refl. Qed.
Lemma D_882b4 : decode_any W_882b4 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882b8 : bv 32 := 0x03013903.
Lemma F_882b8 : fetch_word Plain.M.loaded_segments (0x88310 : word) = Some W_882b8.
Proof. vm_refl. Qed.
Lemma D_882b8 : decode_any W_882b8 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882bc : bv 32 := 0x02813983.
Lemma F_882bc : fetch_word Plain.M.loaded_segments (0x88314 : word) = Some W_882bc.
Proof. vm_refl. Qed.
Lemma D_882bc : decode_any W_882bc = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882c0 : bv 32 := 0x02013a03.
Lemma F_882c0 : fetch_word Plain.M.loaded_segments (0x88318 : word) = Some W_882c0.
Proof. vm_refl. Qed.
Lemma D_882c0 : decode_any W_882c0 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882c4 : bv 32 := 0x01813a83.
Lemma F_882c4 : fetch_word Plain.M.loaded_segments (0x8831c : word) = Some W_882c4.
Proof. vm_refl. Qed.
Lemma D_882c4 : decode_any W_882c4 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882c8 : bv 32 := 0x05010113.
Lemma F_882c8 : fetch_word Plain.M.loaded_segments (0x88320 : word) = Some W_882c8.
Proof. vm_refl. Qed.
Lemma D_882c8 : decode_any W_882c8 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_882cc : bv 32 := 0x00008067.
Lemma F_882cc : fetch_word Plain.M.loaded_segments (0x88324 : word) = Some W_882cc.
Proof. vm_refl. Qed.
Lemma D_882cc : decode_any W_882cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
