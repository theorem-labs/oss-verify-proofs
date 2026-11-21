(* reloc-zl14c *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition TW_1a0e8 : bv 32 := 0x0089b583.
Lemma TF_1a0e8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0f4 : word) = Some TW_1a0e8.
Proof. vm_refl. Qed.
Lemma TD_1a0e8 : decode_any TW_1a0e8 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0ec : bv 32 := 0x0109b603.
Lemma TF_1a0ec : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0f8 : word) = Some TW_1a0ec.
Proof. vm_refl. Qed.
Lemma TD_1a0ec : decode_any TW_1a0ec = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0f0 : bv 32 := 0x00a40533.
Lemma TF_1a0f0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a0fc : word) = Some TW_1a0f0.
Proof. vm_refl. Qed.
Lemma TD_1a0f0 : decode_any TW_1a0f0 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0f4 : bv 32 := 0x350070ef.
Lemma TF_1a0f4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a100 : word) = Some TW_1a0f4.
Proof. vm_refl. Qed.
Lemma TD_1a0f4 : decode_any TW_1a0f4 = Some (Jal 1 29520, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0f8 : bv 32 := 0x0009b983.
Lemma TF_1a0f8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a104 : word) = Some TW_1a0f8.
Proof. vm_refl. Qed.
Lemma TD_1a0f8 : decode_any TW_1a0f8 = Some (Load SZ8 true 19 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a0fc : bv 32 := 0x008a8a93.
Lemma TF_1a0fc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a108 : word) = Some TW_1a0fc.
Proof. vm_refl. Qed.
Lemma TD_1a0fc : decode_any TW_1a0fc = Some (OpImm ALU_ADD 21 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a100 : bv 32 := 0xfc0998e3.
Lemma TF_1a100 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a10c : word) = Some TW_1a100.
Proof. vm_refl. Qed.
Lemma TD_1a100 : decode_any TW_1a100 = Some (Branch BC_NE 19 0 8144, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a104 : bv 32 := 0x0284b603.
Lemma TF_1a104 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a110 : word) = Some TW_1a104.
Proof. vm_refl. Qed.
Lemma TD_1a104 : decode_any TW_1a104 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a108 : bv 32 := 0x00ca3023.
Lemma TF_1a108 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a114 : word) = Some TW_1a108.
Proof. vm_refl. Qed.
Lemma TD_1a108 : decode_any TW_1a108 = Some (Store SZ8 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a10c : bv 32 := 0x0d493023.
Lemma TF_1a10c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a118 : word) = Some TW_1a10c.
Proof. vm_refl. Qed.
Lemma TD_1a10c : decode_any TW_1a10c = Some (Store SZ8 18 20 192, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a110 : bv 32 := 0x01293023.
Lemma TF_1a110 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a11c : word) = Some TW_1a110.
Proof. vm_refl. Qed.
Lemma TD_1a110 : decode_any TW_1a110 = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a114 : bv 32 := 0x00040513.
Lemma TF_1a114 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a120 : word) = Some TW_1a114.
Proof. vm_refl. Qed.
Lemma TD_1a114 : decode_any TW_1a114 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a118 : bv 32 := 0x45d070ef.
Lemma TF_1a118 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a124 : word) = Some TW_1a118.
Proof. vm_refl. Qed.
Lemma TD_1a118 : decode_any TW_1a118 = Some (Jal 1 31836, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a11c : bv 32 := 0x04054a63.
Lemma TF_1a11c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a128 : word) = Some TW_1a11c.
Proof. vm_refl. Qed.
Lemma TD_1a11c : decode_any TW_1a11c = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a120 : bv 32 := 0x00051663.
Lemma TF_1a120 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a12c : word) = Some TW_1a120.
Proof. vm_refl. Qed.
Lemma TD_1a120 : decode_any TW_1a120 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a124 : bv 32 := 0x00100513.
Lemma TF_1a124 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a130 : word) = Some TW_1a124.
Proof. vm_refl. Qed.
Lemma TD_1a124 : decode_any TW_1a124 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a128 : bv 32 := 0x00a48023.
Lemma TF_1a128 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a134 : word) = Some TW_1a128.
Proof. vm_refl. Qed.
Lemma TD_1a128 : decode_any TW_1a128 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a12c : bv 32 := 0x00200513.
Lemma TF_1a12c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a138 : word) = Some TW_1a12c.
Proof. vm_refl. Qed.
Lemma TD_1a12c : decode_any TW_1a12c = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a130 : bv 32 := 0x0007a597.
Lemma TF_1a130 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a13c : word) = Some TW_1a130.
Proof. vm_refl. Qed.
Lemma TD_1a130 : decode_any TW_1a130 = Some (Auipc 11 122, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a134 : bv 32 := 0x02a92423.
Lemma TF_1a134 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a140 : word) = Some TW_1a134.
Proof. vm_refl. Qed.
Lemma TD_1a134 : decode_any TW_1a134 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a138 : bv 32 := 0x06000893.
Lemma TF_1a138 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a144 : word) = Some TW_1a138.
Proof. vm_refl. Qed.
Lemma TD_1a138 : decode_any TW_1a138 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a13c : bv 32 := 0x11c58513.
Lemma TF_1a13c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a148 : word) = Some TW_1a13c.
Proof. vm_refl. Qed.
Lemma TD_1a13c : decode_any TW_1a13c = Some (OpImm ALU_ADD 10 11 284, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a140 : bv 32 := 0x03848593.
Lemma TF_1a140 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a14c : word) = Some TW_1a140.
Proof. vm_refl. Qed.
Lemma TD_1a140 : decode_any TW_1a140 = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a144 : bv 32 := 0x00000073.
Lemma TF_1a144 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a150 : word) = Some TW_1a144.
Proof. vm_refl. Qed.
Lemma TD_1a144 : decode_any TW_1a144 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_1a144 : is_ecall TW_1a144 = true.
Proof. reflexivity. Qed.

Definition TW_1a148 : bv 32 := 0x07890613.
Lemma TF_1a148 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a154 : word) = Some TW_1a148.
Proof. vm_refl. Qed.
Lemma TD_1a148 : decode_any TW_1a148 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a14c : bv 32 := 0x02a92023.
Lemma TF_1a14c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a158 : word) = Some TW_1a14c.
Proof. vm_refl. Qed.
Lemma TD_1a14c : decode_any TW_1a14c = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a150 : bv 32 := 0x08b93c23.
Lemma TF_1a150 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a15c : word) = Some TW_1a150.
Proof. vm_refl. Qed.
Lemma TD_1a150 : decode_any TW_1a150 = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a154 : bv 32 := 0x06c93c23.
Lemma TF_1a154 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a160 : word) = Some TW_1a154.
Proof. vm_refl. Qed.
Lemma TD_1a154 : decode_any TW_1a154 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a158 : bv 32 := 0x0007a517.
Lemma TF_1a158 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a164 : word) = Some TW_1a158.
Proof. vm_refl. Qed.
Lemma TD_1a158 : decode_any TW_1a158 = Some (Auipc 10 122, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a15c : bv 32 := 0x35c53503.
Lemma TF_1a15c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a168 : word) = Some TW_1a15c.
Proof. vm_refl. Qed.
Lemma TD_1a15c : decode_any TW_1a15c = Some (Load SZ8 true 10 10 860, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a160 : bv 32 := 0x01293423.
Lemma TF_1a160 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a16c : word) = Some TW_1a160.
Proof. vm_refl. Qed.
Lemma TD_1a160 : decode_any TW_1a160 = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a164 : bv 32 := 0x01293823.
Lemma TF_1a164 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a170 : word) = Some TW_1a164.
Proof. vm_refl. Qed.
Lemma TD_1a164 : decode_any TW_1a164 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a168 : bv 32 := 0x00a93c23.
Lemma TF_1a168 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a174 : word) = Some TW_1a168.
Proof. vm_refl. Qed.
Lemma TD_1a168 : decode_any TW_1a168 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a16c : bv 32 := 0x0080006f.
Lemma TF_1a16c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a178 : word) = Some TW_1a16c.
Proof. vm_refl. Qed.
Lemma TD_1a16c : decode_any TW_1a16c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a170 : bv 32 := 0x00000023.
Lemma TF_1a170 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a17c : word) = Some TW_1a170.
Proof. vm_refl. Qed.
Lemma TD_1a170 : decode_any TW_1a170 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a174 : bv 32 := 0x03813083.
Lemma TF_1a174 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a180 : word) = Some TW_1a174.
Proof. vm_refl. Qed.
Lemma TD_1a174 : decode_any TW_1a174 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a178 : bv 32 := 0x03013403.
Lemma TF_1a178 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a184 : word) = Some TW_1a178.
Proof. vm_refl. Qed.
Lemma TD_1a178 : decode_any TW_1a178 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a17c : bv 32 := 0x02813483.
Lemma TF_1a17c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a188 : word) = Some TW_1a17c.
Proof. vm_refl. Qed.
Lemma TD_1a17c : decode_any TW_1a17c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a180 : bv 32 := 0x02013903.
Lemma TF_1a180 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a18c : word) = Some TW_1a180.
Proof. vm_refl. Qed.
Lemma TD_1a180 : decode_any TW_1a180 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a184 : bv 32 := 0x01813983.
Lemma TF_1a184 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a190 : word) = Some TW_1a184.
Proof. vm_refl. Qed.
Lemma TD_1a184 : decode_any TW_1a184 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a188 : bv 32 := 0x01013a03.
Lemma TF_1a188 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a194 : word) = Some TW_1a188.
Proof. vm_refl. Qed.
Lemma TD_1a188 : decode_any TW_1a188 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a18c : bv 32 := 0x00813a83.
Lemma TF_1a18c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a198 : word) = Some TW_1a18c.
Proof. vm_refl. Qed.
Lemma TD_1a18c : decode_any TW_1a18c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a190 : bv 32 := 0x04010113.
Lemma TF_1a190 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a19c : word) = Some TW_1a190.
Proof. vm_refl. Qed.
Lemma TD_1a190 : decode_any TW_1a190 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a194 : bv 32 := 0x00008067.
Lemma TF_1a194 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1a0 : word) = Some TW_1a194.
Proof. vm_refl. Qed.
Lemma TD_1a194 : decode_any TW_1a194 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0bc : bv 32 := 0xfd010113.
Lemma F_1a0bc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1a4 : word) = Some W_1a0bc.
Proof. vm_refl. Qed.
Lemma D_1a0bc : decode_any W_1a0bc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0c0 : bv 32 := 0x02113423.
Lemma F_1a0c0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1a8 : word) = Some W_1a0c0.
Proof. vm_refl. Qed.
Lemma D_1a0c0 : decode_any W_1a0c0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0c4 : bv 32 := 0x02813023.
Lemma F_1a0c4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1ac : word) = Some W_1a0c4.
Proof. vm_refl. Qed.
Lemma D_1a0c4 : decode_any W_1a0c4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0c8 : bv 32 := 0x00913c23.
Lemma F_1a0c8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1b0 : word) = Some W_1a0c8.
Proof. vm_refl. Qed.
Lemma D_1a0c8 : decode_any W_1a0c8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0cc : bv 32 := 0x01213823.
Lemma F_1a0cc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1b4 : word) = Some W_1a0cc.
Proof. vm_refl. Qed.
Lemma D_1a0cc : decode_any W_1a0cc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0d0 : bv 32 := 0x01313423.
Lemma F_1a0d0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1b8 : word) = Some W_1a0d0.
Proof. vm_refl. Qed.
Lemma D_1a0d0 : decode_any W_1a0d0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0d4 : bv 32 := 0x0007a517.
Lemma F_1a0d4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1bc : word) = Some W_1a0d4.
Proof. vm_refl. Qed.
Lemma D_1a0d4 : decode_any W_1a0d4 = Some (Auipc 10 122, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0d8 : bv 32 := 0x0d450913.
Lemma F_1a0d8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1c0 : word) = Some W_1a0d8.
Proof. vm_refl. Qed.
Lemma D_1a0d8 : decode_any W_1a0d8 = Some (OpImm ALU_ADD 18 10 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0dc : bv 32 := 0x00490413.
Lemma F_1a0dc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1c4 : word) = Some W_1a0dc.
Proof. vm_refl. Qed.
Lemma D_1a0dc : decode_any W_1a0dc = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0e0 : bv 32 := 0x00040513.
Lemma F_1a0e0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1c8 : word) = Some W_1a0e0.
Proof. vm_refl. Qed.
Lemma D_1a0e0 : decode_any W_1a0e0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0e4 : bv 32 := 0x091070ef.
Lemma F_1a0e4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1cc : word) = Some W_1a0e4.
Proof. vm_refl. Qed.
Lemma D_1a0e4 : decode_any W_1a0e4 = Some (Jal 1 30864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0e8 : bv 32 := 0x01093503.
Lemma F_1a0e8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1d0 : word) = Some W_1a0e8.
Proof. vm_refl. Qed.
Lemma D_1a0e8 : decode_any W_1a0e8 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0ec : bv 32 := 0x06050863.
Lemma F_1a0ec : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1d4 : word) = Some W_1a0ec.
Proof. vm_refl. Qed.
Lemma D_1a0ec : decode_any W_1a0ec = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0f0 : bv 32 := 0x00892583.
Lemma F_1a0f0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1d8 : word) = Some W_1a0f0.
Proof. vm_refl. Qed.
Lemma D_1a0f0 : decode_any W_1a0f0 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0f4 : bv 32 := 0x0180006f.
Lemma F_1a0f4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1dc : word) = Some W_1a0f4.
Proof. vm_refl. Qed.
Lemma D_1a0f4 : decode_any W_1a0f4 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0f8 : bv 32 := 0x00053503.
Lemma F_1a0f8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1e0 : word) = Some W_1a0f8.
Proof. vm_refl. Qed.
Lemma D_1a0f8 : decode_any W_1a0f8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a0fc : bv 32 := 0x02000593.
Lemma F_1a0fc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1e4 : word) = Some W_1a0fc.
Proof. vm_refl. Qed.
Lemma D_1a0fc : decode_any W_1a0fc = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a100 : bv 32 := 0x00b92423.
Lemma F_1a100 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1e8 : word) = Some W_1a100.
Proof. vm_refl. Qed.
Lemma D_1a100 : decode_any W_1a100 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a104 : bv 32 := 0x00a93823.
Lemma F_1a104 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1ec : word) = Some W_1a104.
Proof. vm_refl. Qed.
Lemma D_1a104 : decode_any W_1a104 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a108 : bv 32 := 0x04050a63.
Lemma F_1a108 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1f0 : word) = Some W_1a108.
Proof. vm_refl. Qed.
Lemma D_1a108 : decode_any W_1a108 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a10c : bv 32 := 0xfff5861b.
Lemma F_1a10c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1f4 : word) = Some W_1a10c.
Proof. vm_refl. Qed.
Lemma D_1a10c : decode_any W_1a10c = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a110 : bv 32 := 0x00c92423.
Lemma F_1a110 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1f8 : word) = Some W_1a110.
Proof. vm_refl. Qed.
Lemma D_1a110 : decode_any W_1a110 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a114 : bv 32 := 0xfeb052e3.
Lemma F_1a114 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a1fc : word) = Some W_1a114.
Proof. vm_refl. Qed.
Lemma D_1a114 : decode_any W_1a114 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a118 : bv 32 := 0x01093503.
Lemma F_1a118 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a200 : word) = Some W_1a118.
Proof. vm_refl. Qed.
Lemma D_1a118 : decode_any W_1a118 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a11c : bv 32 := 0x00361613.
Lemma F_1a11c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a204 : word) = Some W_1a11c.
Proof. vm_refl. Qed.
Lemma D_1a11c : decode_any W_1a11c = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a120 : bv 32 := 0x00c50533.
Lemma F_1a120 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a208 : word) = Some W_1a120.
Proof. vm_refl. Qed.
Lemma D_1a120 : decode_any W_1a120 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a124 : bv 32 := 0x00853983.
Lemma F_1a124 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a20c : word) = Some W_1a124.
Proof. vm_refl. Qed.
Lemma D_1a124 : decode_any W_1a124 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a128 : bv 32 := 0x10853483.
Lemma F_1a128 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a210 : word) = Some W_1a128.
Proof. vm_refl. Qed.
Lemma D_1a128 : decode_any W_1a128 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a12c : bv 32 := 0x00040513.
Lemma F_1a12c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a214 : word) = Some W_1a12c.
Proof. vm_refl. Qed.
Lemma D_1a12c : decode_any W_1a12c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a130 : bv 32 := 0x2cd070ef.
Lemma F_1a130 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a218 : word) = Some W_1a130.
Proof. vm_refl. Qed.
Lemma D_1a130 : decode_any W_1a130 = Some (Jal 1 31436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a134 : bv 32 := 0x00048513.
Lemma F_1a134 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a21c : word) = Some W_1a134.
Proof. vm_refl. Qed.
Lemma D_1a134 : decode_any W_1a134 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a138 : bv 32 := 0x000980e7.
Lemma F_1a138 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a220 : word) = Some W_1a138.
Proof. vm_refl. Qed.
Lemma D_1a138 : decode_any W_1a138 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a13c : bv 32 := 0x00040513.
Lemma F_1a13c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a224 : word) = Some W_1a13c.
Proof. vm_refl. Qed.
Lemma D_1a13c : decode_any W_1a13c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a140 : bv 32 := 0x035070ef.
Lemma F_1a140 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a228 : word) = Some W_1a140.
Proof. vm_refl. Qed.
Lemma D_1a140 : decode_any W_1a140 = Some (Jal 1 30772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a144 : bv 32 := 0x00892503.
Lemma F_1a144 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a22c : word) = Some W_1a144.
Proof. vm_refl. Qed.
Lemma D_1a144 : decode_any W_1a144 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a148 : bv 32 := 0xfff5061b.
Lemma F_1a148 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a230 : word) = Some W_1a148.
Proof. vm_refl. Qed.
Lemma D_1a148 : decode_any W_1a148 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a14c : bv 32 := 0x00c92423.
Lemma F_1a14c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a234 : word) = Some W_1a14c.
Proof. vm_refl. Qed.
Lemma D_1a14c : decode_any W_1a14c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a150 : bv 32 := 0xfca044e3.
Lemma F_1a150 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a238 : word) = Some W_1a150.
Proof. vm_refl. Qed.
Lemma D_1a150 : decode_any W_1a150 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a154 : bv 32 := 0x01093503.
Lemma F_1a154 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a23c : word) = Some W_1a154.
Proof. vm_refl. Qed.
Lemma D_1a154 : decode_any W_1a154 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a158 : bv 32 := 0xfa1ff06f.
Lemma F_1a158 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a240 : word) = Some W_1a158.
Proof. vm_refl. Qed.
Lemma D_1a158 : decode_any W_1a158 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a15c : bv 32 := 0x00100513.
Lemma F_1a15c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a244 : word) = Some W_1a15c.
Proof. vm_refl. Qed.
Lemma D_1a15c : decode_any W_1a15c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a160 : bv 32 := 0x00a90023.
Lemma F_1a160 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a248 : word) = Some W_1a160.
Proof. vm_refl. Qed.
Lemma D_1a160 : decode_any W_1a160 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a164 : bv 32 := 0x00040513.
Lemma F_1a164 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a24c : word) = Some W_1a164.
Proof. vm_refl. Qed.
Lemma D_1a164 : decode_any W_1a164 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a168 : bv 32 := 0x02813083.
Lemma F_1a168 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a250 : word) = Some W_1a168.
Proof. vm_refl. Qed.
Lemma D_1a168 : decode_any W_1a168 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a16c : bv 32 := 0x02013403.
Lemma F_1a16c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a254 : word) = Some W_1a16c.
Proof. vm_refl. Qed.
Lemma D_1a16c : decode_any W_1a16c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a170 : bv 32 := 0x01813483.
Lemma F_1a170 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a258 : word) = Some W_1a170.
Proof. vm_refl. Qed.
Lemma D_1a170 : decode_any W_1a170 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a174 : bv 32 := 0x01013903.
Lemma F_1a174 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a25c : word) = Some W_1a174.
Proof. vm_refl. Qed.
Lemma D_1a174 : decode_any W_1a174 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a178 : bv 32 := 0x00813983.
Lemma F_1a178 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a260 : word) = Some W_1a178.
Proof. vm_refl. Qed.
Lemma D_1a178 : decode_any W_1a178 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a17c : bv 32 := 0x03010113.
Lemma F_1a17c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a264 : word) = Some W_1a17c.
Proof. vm_refl. Qed.
Lemma D_1a17c : decode_any W_1a17c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a180 : bv 32 := 0x27d0706f.
Lemma F_1a180 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a268 : word) = Some W_1a180.
Proof. vm_refl. Qed.
Lemma D_1a180 : decode_any W_1a180 = Some (Jal 0 31356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a184 : bv 32 := 0x00008067.
Lemma F_1a184 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a26c : word) = Some W_1a184.
Proof. vm_refl. Qed.
Lemma D_1a184 : decode_any W_1a184 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a24c : bv 32 := 0x00050067.
Lemma F_1a24c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a334 : word) = Some W_1a24c.
Proof. vm_refl. Qed.
Lemma D_1a24c : decode_any W_1a24c = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a250 : bv 32 := 0x00008067.
Lemma F_1a250 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a338 : word) = Some W_1a250.
Proof. vm_refl. Qed.
Lemma D_1a250 : decode_any W_1a250 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a254 : bv 32 := 0xfe010113.
Lemma F_1a254 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a33c : word) = Some W_1a254.
Proof. vm_refl. Qed.
Lemma D_1a254 : decode_any W_1a254 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a258 : bv 32 := 0x00113c23.
Lemma F_1a258 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a340 : word) = Some W_1a258.
Proof. vm_refl. Qed.
Lemma D_1a258 : decode_any W_1a258 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a25c : bv 32 := 0x00813823.
Lemma F_1a25c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a344 : word) = Some W_1a25c.
Proof. vm_refl. Qed.
Lemma D_1a25c : decode_any W_1a25c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a260 : bv 32 := 0x00913423.
Lemma F_1a260 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a348 : word) = Some W_1a260.
Proof. vm_refl. Qed.
Lemma D_1a260 : decode_any W_1a260 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a264 : bv 32 := 0x00009517.
Lemma F_1a264 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a34c : word) = Some W_1a264.
Proof. vm_refl. Qed.
Lemma D_1a264 : decode_any W_1a264 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a268 : bv 32 := 0x00009597.
Lemma F_1a268 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a350 : word) = Some W_1a268.
Proof. vm_refl. Qed.
Lemma D_1a268 : decode_any W_1a268 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a26c : bv 32 := 0xb8c53503.
Lemma F_1a26c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a354 : word) = Some W_1a26c.
Proof. vm_refl. Qed.
Lemma D_1a26c : decode_any W_1a26c = Some (Load SZ8 true 10 10 2956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a270 : bv 32 := 0xb905b403.
Lemma F_1a270 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a358 : word) = Some W_1a270.
Proof. vm_refl. Qed.
Lemma D_1a270 : decode_any W_1a270 = Some (Load SZ8 true 8 11 2960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a274 : bv 32 := 0x00a47c63.
Lemma F_1a274 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a35c : word) = Some W_1a274.
Proof. vm_refl. Qed.
Lemma D_1a274 : decode_any W_1a274 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a278 : bv 32 := 0xff853583.
Lemma F_1a278 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a360 : word) = Some W_1a278.
Proof. vm_refl. Qed.
Lemma D_1a278 : decode_any W_1a278 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a27c : bv 32 := 0xff850493.
Lemma F_1a27c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a364 : word) = Some W_1a27c.
Proof. vm_refl. Qed.
Lemma D_1a27c : decode_any W_1a27c = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a280 : bv 32 := 0x000580e7.
Lemma F_1a280 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a368 : word) = Some W_1a280.
Proof. vm_refl. Qed.
Lemma D_1a280 : decode_any W_1a280 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a284 : bv 32 := 0x00048513.
Lemma F_1a284 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a36c : word) = Some W_1a284.
Proof. vm_refl. Qed.
Lemma D_1a284 : decode_any W_1a284 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a288 : bv 32 := 0xfe9468e3.
Lemma F_1a288 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a370 : word) = Some W_1a288.
Proof. vm_refl. Qed.
Lemma D_1a288 : decode_any W_1a288 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a28c : bv 32 := 0x01813083.
Lemma F_1a28c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a374 : word) = Some W_1a28c.
Proof. vm_refl. Qed.
Lemma D_1a28c : decode_any W_1a28c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a290 : bv 32 := 0x01013403.
Lemma F_1a290 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a378 : word) = Some W_1a290.
Proof. vm_refl. Qed.
Lemma D_1a290 : decode_any W_1a290 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a294 : bv 32 := 0x00813483.
Lemma F_1a294 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a37c : word) = Some W_1a294.
Proof. vm_refl. Qed.
Lemma D_1a294 : decode_any W_1a294 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a298 : bv 32 := 0x02010113.
Lemma F_1a298 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a380 : word) = Some W_1a298.
Proof. vm_refl. Qed.
Lemma D_1a298 : decode_any W_1a298 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a29c : bv 32 := 0xfb5ff06f.
Lemma F_1a29c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a384 : word) = Some W_1a29c.
Proof. vm_refl. Qed.
Lemma D_1a29c : decode_any W_1a29c = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2a0 : bv 32 := 0xff010113.
Lemma F_1a2a0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a388 : word) = Some W_1a2a0.
Proof. vm_refl. Qed.
Lemma D_1a2a0 : decode_any W_1a2a0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2a4 : bv 32 := 0x00113423.
Lemma F_1a2a4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a38c : word) = Some W_1a2a4.
Proof. vm_refl. Qed.
Lemma D_1a2a4 : decode_any W_1a2a4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2a8 : bv 32 := 0x00813023.
Lemma F_1a2a8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a390 : word) = Some W_1a2a8.
Proof. vm_refl. Qed.
Lemma D_1a2a8 : decode_any W_1a2a8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2ac : bv 32 := 0x00000593.
Lemma F_1a2ac : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a394 : word) = Some W_1a2ac.
Proof. vm_refl. Qed.
Lemma D_1a2ac : decode_any W_1a2ac = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2b0 : bv 32 := 0x00020613.
Lemma F_1a2b0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a398 : word) = Some W_1a2b0.
Proof. vm_refl. Qed.
Lemma D_1a2b0 : decode_any W_1a2b0 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2b4 : bv 32 := 0xf5862603.
Lemma F_1a2b4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a39c : word) = Some W_1a2b4.
Proof. vm_refl. Qed.
Lemma D_1a2b4 : decode_any W_1a2b4 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2b8 : bv 32 := 0x0007a697.
Lemma F_1a2b8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3a0 : word) = Some W_1a2b8.
Proof. vm_refl. Qed.
Lemma D_1a2b8 : decode_any W_1a2b8 = Some (Auipc 13 122, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2bc : bv 32 := 0x11068693.
Lemma F_1a2bc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3a4 : word) = Some W_1a2bc.
Proof. vm_refl. Qed.
Lemma D_1a2bc : decode_any W_1a2bc = Some (OpImm ALU_ADD 13 13 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2c0 : bv 32 := 0x1606a72f.
Lemma F_1a2c0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3a8 : word) = Some W_1a2c0.
Proof. vm_refl. Qed.
Lemma D_1a2c0 : decode_any W_1a2c0 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2c4 : bv 32 := 0x00b71663.
Lemma F_1a2c4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3ac : word) = Some W_1a2c4.
Proof. vm_refl. Qed.
Lemma D_1a2c4 : decode_any W_1a2c4 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2c8 : bv 32 := 0x1ec6a7af.
Lemma F_1a2c8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3b0 : word) = Some W_1a2c8.
Proof. vm_refl. Qed.
Lemma D_1a2c8 : decode_any W_1a2c8 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2cc : bv 32 := 0xfe079ae3.
Lemma F_1a2cc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3b4 : word) = Some W_1a2cc.
Proof. vm_refl. Qed.
Lemma D_1a2cc : decode_any W_1a2cc = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2d0 : bv 32 := 0x0007059b.
Lemma F_1a2d0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3b8 : word) = Some W_1a2d0.
Proof. vm_refl. Qed.
Lemma D_1a2d0 : decode_any W_1a2d0 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2d4 : bv 32 := 0x02c58263.
Lemma F_1a2d4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3bc : word) = Some W_1a2d4.
Proof. vm_refl. Qed.
Lemma D_1a2d4 : decode_any W_1a2d4 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2d8 : bv 32 := 0x02058263.
Lemma F_1a2d8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3c0 : word) = Some W_1a2d8.
Proof. vm_refl. Qed.
Lemma D_1a2d8 : decode_any W_1a2d8 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2dc : bv 32 := 0x04900893.
Lemma F_1a2dc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3c4 : word) = Some W_1a2dc.
Proof. vm_refl. Qed.
Lemma D_1a2dc : decode_any W_1a2dc = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2e0 : bv 32 := 0x00000593.
Lemma F_1a2e0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3c8 : word) = Some W_1a2e0.
Proof. vm_refl. Qed.
Lemma D_1a2e0 : decode_any W_1a2e0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2e4 : bv 32 := 0x00000613.
Lemma F_1a2e4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3cc : word) = Some W_1a2e4.
Proof. vm_refl. Qed.
Lemma D_1a2e4 : decode_any W_1a2e4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2e8 : bv 32 := 0x00000693.
Lemma F_1a2e8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3d0 : word) = Some W_1a2e8.
Proof. vm_refl. Qed.
Lemma D_1a2e8 : decode_any W_1a2e8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2ec : bv 32 := 0x00000513.
Lemma F_1a2ec : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3d4 : word) = Some W_1a2ec.
Proof. vm_refl. Qed.
Lemma D_1a2ec : decode_any W_1a2ec = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2f0 : bv 32 := 0x00000073.
Lemma F_1a2f0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3d8 : word) = Some W_1a2f0.
Proof. vm_refl. Qed.
Lemma D_1a2f0 : decode_any W_1a2f0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1a2f0 : is_ecall W_1a2f0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1a2f4 : bv 32 := 0xff9ff06f.
Lemma F_1a2f4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3dc : word) = Some W_1a2f4.
Proof. vm_refl. Qed.
Lemma D_1a2f4 : decode_any W_1a2f4 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2f8 : bv 32 := 0x00000023.
Lemma F_1a2f8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3e0 : word) = Some W_1a2f8.
Proof. vm_refl. Qed.
Lemma D_1a2f8 : decode_any W_1a2f8 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2fc : bv 32 := 0x00050413.
Lemma F_1a2fc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3e4 : word) = Some W_1a2fc.
Proof. vm_refl. Qed.
Lemma D_1a2fc : decode_any W_1a2fc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a300 : bv 32 := 0xdbdff0ef.
Lemma F_1a300 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3e8 : word) = Some W_1a300.
Proof. vm_refl. Qed.
Lemma D_1a300 : decode_any W_1a300 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a304 : bv 32 := 0xf51ff0ef.
Lemma F_1a304 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3ec : word) = Some W_1a304.
Proof. vm_refl. Qed.
Lemma D_1a304 : decode_any W_1a304 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a308 : bv 32 := 0x258020ef.
Lemma F_1a308 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3f0 : word) = Some W_1a308.
Proof. vm_refl. Qed.
Lemma D_1a308 : decode_any W_1a308 = Some (Jal 1 8792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a30c : bv 32 := 0x00040513.
Lemma F_1a30c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3f4 : word) = Some W_1a30c.
Proof. vm_refl. Qed.
Lemma D_1a30c : decode_any W_1a30c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a310 : bv 32 := 0x004000ef.
Lemma F_1a310 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3f8 : word) = Some W_1a310.
Proof. vm_refl. Qed.
Lemma D_1a310 : decode_any W_1a310 = Some (Jal 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a314 : bv 32 := 0x00050593.
Lemma F_1a314 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a3fc : word) = Some W_1a314.
Proof. vm_refl. Qed.
Lemma D_1a314 : decode_any W_1a314 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a318 : bv 32 := 0x05e00893.
Lemma F_1a318 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a400 : word) = Some W_1a318.
Proof. vm_refl. Qed.
Lemma D_1a318 : decode_any W_1a318 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a31c : bv 32 := 0x00000073.
Lemma F_1a31c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a404 : word) = Some W_1a31c.
Proof. vm_refl. Qed.
Lemma D_1a31c : decode_any W_1a31c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1a31c : is_ecall W_1a31c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1a414 : bv 32 := 0xff010113.
Lemma F_1a414 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a4fc : word) = Some W_1a414.
Proof. vm_refl. Qed.
Lemma D_1a414 : decode_any W_1a414 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a418 : bv 32 := 0x00113423.
Lemma F_1a418 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a500 : word) = Some W_1a418.
Proof. vm_refl. Qed.
Lemma D_1a418 : decode_any W_1a418 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a41c : bv 32 := 0x00050e63.
Lemma F_1a41c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a504 : word) = Some W_1a41c.
Proof. vm_refl. Qed.
Lemma D_1a41c : decode_any W_1a41c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a420 : bv 32 := 0x00050593.
Lemma F_1a420 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a508 : word) = Some W_1a420.
Proof. vm_refl. Qed.
Lemma D_1a420 : decode_any W_1a420 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a424 : bv 32 := 0x00009517.
Lemma F_1a424 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a50c : word) = Some W_1a424.
Proof. vm_refl. Qed.
Lemma D_1a424 : decode_any W_1a424 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a428 : bv 32 := 0x9c453503.
Lemma F_1a428 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a510 : word) = Some W_1a428.
Proof. vm_refl. Qed.
Lemma D_1a428 : decode_any W_1a428 = Some (Load SZ8 true 10 10 2500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a42c : bv 32 := 0x00800613.
Lemma F_1a42c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a514 : word) = Some W_1a42c.
Proof. vm_refl. Qed.
Lemma D_1a42c : decode_any W_1a42c = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a430 : bv 32 := 0x739060ef.
Lemma F_1a430 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a518 : word) = Some W_1a430.
Proof. vm_refl. Qed.
Lemma D_1a430 : decode_any W_1a430 = Some (Jal 1 28472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a434 : bv 32 := 0x01c0006f.
Lemma F_1a434 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a51c : word) = Some W_1a434.
Proof. vm_refl. Qed.
Lemma D_1a434 : decode_any W_1a434 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a438 : bv 32 := 0x00009517.
Lemma F_1a438 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a520 : word) = Some W_1a438.
Proof. vm_refl. Qed.
Lemma D_1a438 : decode_any W_1a438 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a43c : bv 32 := 0x9b053503.
Lemma F_1a43c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a524 : word) = Some W_1a43c.
Proof. vm_refl. Qed.
Lemma D_1a43c : decode_any W_1a43c = Some (Load SZ8 true 10 10 2480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a440 : bv 32 := 0x41c655b7.
Lemma F_1a440 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a528 : word) = Some W_1a440.
Proof. vm_refl. Qed.
Lemma D_1a440 : decode_any W_1a440 = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a444 : bv 32 := 0xe6d5859b.
Lemma F_1a444 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a52c : word) = Some W_1a444.
Proof. vm_refl. Qed.
Lemma D_1a444 : decode_any W_1a444 = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a448 : bv 32 := 0x02b505b3.
Lemma F_1a448 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a530 : word) = Some W_1a448.
Proof. vm_refl. Qed.
Lemma D_1a448 : decode_any W_1a448 = Some (Mul M_MUL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a44c : bv 32 := 0x00b53023.
Lemma F_1a44c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a534 : word) = Some W_1a44c.
Proof. vm_refl. Qed.
Lemma D_1a44c : decode_any W_1a44c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a450 : bv 32 := 0x00009517.
Lemma F_1a450 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a538 : word) = Some W_1a450.
Proof. vm_refl. Qed.
Lemma D_1a450 : decode_any W_1a450 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a454 : bv 32 := 0x99853503.
Lemma F_1a454 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a53c : word) = Some W_1a454.
Proof. vm_refl. Qed.
Lemma D_1a454 : decode_any W_1a454 = Some (Load SZ8 true 10 10 2456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a458 : bv 32 := 0x000500a3.
Lemma F_1a458 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a540 : word) = Some W_1a458.
Proof. vm_refl. Qed.
Lemma D_1a458 : decode_any W_1a458 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a45c : bv 32 := 0x00053503.
Lemma F_1a45c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a544 : word) = Some W_1a45c.
Proof. vm_refl. Qed.
Lemma D_1a45c : decode_any W_1a45c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a460 : bv 32 := 0x00020593.
Lemma F_1a460 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a548 : word) = Some W_1a460.
Proof. vm_refl. Qed.
Lemma D_1a460 : decode_any W_1a460 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a464 : bv 32 := 0xfea5b823.
Lemma F_1a464 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a54c : word) = Some W_1a464.
Proof. vm_refl. Qed.
Lemma D_1a464 : decode_any W_1a464 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a468 : bv 32 := 0x00813083.
Lemma F_1a468 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a550 : word) = Some W_1a468.
Proof. vm_refl. Qed.
Lemma D_1a468 : decode_any W_1a468 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a46c : bv 32 := 0x01010113.
Lemma F_1a46c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a554 : word) = Some W_1a46c.
Proof. vm_refl. Qed.
Lemma D_1a46c : decode_any W_1a46c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a470 : bv 32 := 0x00008067.
Lemma F_1a470 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a558 : word) = Some W_1a470.
Proof. vm_refl. Qed.
Lemma D_1a470 : decode_any W_1a470 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a47c : bv 32 := 0xfffff5b7.
Lemma F_1a47c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a564 : word) = Some W_1a47c.
Proof. vm_refl. Qed.
Lemma D_1a47c : decode_any W_1a47c = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a480 : bv 32 := 0x0015859b.
Lemma F_1a480 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a568 : word) = Some W_1a480.
Proof. vm_refl. Qed.
Lemma D_1a480 : decode_any W_1a480 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a484 : bv 32 := 0x02b56663.
Lemma F_1a484 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a56c : word) = Some W_1a484.
Proof. vm_refl. Qed.
Lemma D_1a484 : decode_any W_1a484 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4b0 : bv 32 := 0x00008067.
Lemma F_1a4b0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a598 : word) = Some W_1a4b0.
Proof. vm_refl. Qed.
Lemma D_1a4b0 : decode_any W_1a4b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a604 : bv 32 := 0x1c050463.
Lemma F_1a604 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a6ec : word) = Some W_1a604.
Proof. vm_refl. Qed.
Lemma D_1a604 : decode_any W_1a604 = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a608 : bv 32 := 0xfd010113.
Lemma F_1a608 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a6f0 : word) = Some W_1a608.
Proof. vm_refl. Qed.
Lemma D_1a608 : decode_any W_1a608 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a60c : bv 32 := 0x02113423.
Lemma F_1a60c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a6f4 : word) = Some W_1a60c.
Proof. vm_refl. Qed.
Lemma D_1a60c : decode_any W_1a60c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a610 : bv 32 := 0x02813023.
Lemma F_1a610 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a6f8 : word) = Some W_1a610.
Proof. vm_refl. Qed.
Lemma D_1a610 : decode_any W_1a610 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a614 : bv 32 := 0x00913c23.
Lemma F_1a614 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a6fc : word) = Some W_1a614.
Proof. vm_refl. Qed.
Lemma D_1a614 : decode_any W_1a614 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a618 : bv 32 := 0x01213823.
Lemma F_1a618 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a700 : word) = Some W_1a618.
Proof. vm_refl. Qed.
Lemma D_1a618 : decode_any W_1a618 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a61c : bv 32 := 0x01313423.
Lemma F_1a61c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a704 : word) = Some W_1a61c.
Proof. vm_refl. Qed.
Lemma D_1a61c : decode_any W_1a61c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a620 : bv 32 := 0x00050493.
Lemma F_1a620 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a708 : word) = Some W_1a620.
Proof. vm_refl. Qed.
Lemma D_1a620 : decode_any W_1a620 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a624 : bv 32 := 0x1ac000ef.
Lemma F_1a624 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a70c : word) = Some W_1a624.
Proof. vm_refl. Qed.
Lemma D_1a624 : decode_any W_1a624 = Some (Jal 1 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a628 : bv 32 := 0x02053583.
Lemma F_1a628 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a710 : word) = Some W_1a628.
Proof. vm_refl. Qed.
Lemma D_1a628 : decode_any W_1a628 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a62c : bv 32 := 0xffd4c683.
Lemma F_1a62c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a714 : word) = Some W_1a62c.
Proof. vm_refl. Qed.
Lemma D_1a62c : decode_any W_1a62c = Some (Load SZ1 false 13 9 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a630 : bv 32 := 0x00c5d613.
Lemma F_1a630 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a718 : word) = Some W_1a630.
Proof. vm_refl. Qed.
Lemma D_1a630 : decode_any W_1a630 = Some (ShiftImm ALU_SRL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a634 : bv 32 := 0x01f6f413.
Lemma F_1a634 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a71c : word) = Some W_1a634.
Proof. vm_refl. Qed.
Lemma D_1a634 : decode_any W_1a634 = Some (OpImm ALU_AND 8 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a638 : bv 32 := 0x00060e63.
Lemma F_1a638 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a720 : word) = Some W_1a638.
Proof. vm_refl. Qed.
Lemma D_1a638 : decode_any W_1a638 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a63c : bv 32 := 0x01f5f613.
Lemma F_1a63c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a724 : word) = Some W_1a63c.
Proof. vm_refl. Qed.
Lemma D_1a63c : decode_any W_1a63c = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a640 : bv 32 := 0x00061a63.
Lemma F_1a640 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a728 : word) = Some W_1a640.
Proof. vm_refl. Qed.
Lemma D_1a640 : decode_any W_1a640 = Some (Branch BC_NE 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a644 : bv 32 := 0xfffff637.
Lemma F_1a644 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a72c : word) = Some W_1a644.
Proof. vm_refl. Qed.
Lemma D_1a644 : decode_any W_1a644 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a648 : bv 32 := 0x00c5f633.
Lemma F_1a648 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a730 : word) = Some W_1a648.
Proof. vm_refl. Qed.
Lemma D_1a648 : decode_any W_1a648 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a64c : bv 32 := 0xff060613.
Lemma F_1a64c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a734 : word) = Some W_1a64c.
Proof. vm_refl. Qed.
Lemma D_1a64c : decode_any W_1a64c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a650 : bv 32 := 0x0200006f.
Lemma F_1a650 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a738 : word) = Some W_1a650.
Proof. vm_refl. Qed.
Lemma D_1a650 : decode_any W_1a650 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a654 : bv 32 := 0x0055d613.
Lemma F_1a654 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a73c : word) = Some W_1a654.
Proof. vm_refl. Qed.
Lemma D_1a654 : decode_any W_1a654 = Some (ShiftImm ALU_SRL 12 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a658 : bv 32 := 0xffff8717.
Lemma F_1a658 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a740 : word) = Some W_1a658.
Proof. vm_refl. Qed.
Lemma D_1a658 : decode_any W_1a658 = Some (Auipc 14 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a65c : bv 32 := 0x07e67613.
Lemma F_1a65c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a744 : word) = Some W_1a65c.
Proof. vm_refl. Qed.
Lemma D_1a65c : decode_any W_1a65c = Some (OpImm ALU_AND 12 12 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a660 : bv 32 := 0xd1c70713.
Lemma F_1a660 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a748 : word) = Some W_1a660.
Proof. vm_refl. Qed.
Lemma D_1a660 : decode_any W_1a660 = Some (OpImm ALU_ADD 14 14 3356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a664 : bv 32 := 0x00c70633.
Lemma F_1a664 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a74c : word) = Some W_1a664.
Proof. vm_refl. Qed.
Lemma D_1a664 : decode_any W_1a664 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a668 : bv 32 := 0x00065603.
Lemma F_1a668 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a750 : word) = Some W_1a668.
Proof. vm_refl. Qed.
Lemma D_1a668 : decode_any W_1a668 = Some (Load SZ2 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a66c : bv 32 := 0x00461613.
Lemma F_1a66c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a754 : word) = Some W_1a66c.
Proof. vm_refl. Qed.
Lemma D_1a66c : decode_any W_1a66c = Some (ShiftImm ALU_SLL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a670 : bv 32 := 0x01053703.
Lemma F_1a670 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a758 : word) = Some W_1a670.
Proof. vm_refl. Qed.
Lemma D_1a670 : decode_any W_1a670 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a674 : bv 32 := 0x028607b3.
Lemma F_1a674 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a75c : word) = Some W_1a674.
Proof. vm_refl. Qed.
Lemma D_1a674 : decode_any W_1a674 = Some (Mul M_MUL 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a678 : bv 32 := 0x0a000813.
Lemma F_1a678 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a760 : word) = Some W_1a678.
Proof. vm_refl. Qed.
Lemma D_1a678 : decode_any W_1a678 = Some (OpImm ALU_ADD 16 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a67c : bv 32 := 0x00c70633.
Lemma F_1a67c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a764 : word) = Some W_1a67c.
Proof. vm_refl. Qed.
Lemma D_1a67c : decode_any W_1a67c = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a680 : bv 32 := 0x00f607b3.
Lemma F_1a680 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a768 : word) = Some W_1a680.
Proof. vm_refl. Qed.
Lemma D_1a680 : decode_any W_1a680 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a684 : bv 32 := 0x00c78613.
Lemma F_1a684 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a76c : word) = Some W_1a684.
Proof. vm_refl. Qed.
Lemma D_1a684 : decode_any W_1a684 = Some (OpImm ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a688 : bv 32 := 0x0056d713.
Lemma F_1a688 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a770 : word) = Some W_1a688.
Proof. vm_refl. Qed.
Lemma D_1a688 : decode_any W_1a688 = Some (ShiftImm ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a68c : bv 32 := 0x0306e663.
Lemma F_1a68c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a774 : word) = Some W_1a68c.
Proof. vm_refl. Qed.
Lemma D_1a68c : decode_any W_1a68c = Some (Branch BC_LTU 13 16 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a690 : bv 32 := 0x00500693.
Lemma F_1a690 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a778 : word) = Some W_1a690.
Proof. vm_refl. Qed.
Lemma D_1a690 : decode_any W_1a690 = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a694 : bv 32 := 0x00d70463.
Lemma F_1a694 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a77c : word) = Some W_1a694.
Proof. vm_refl. Qed.
Lemma D_1a694 : decode_any W_1a694 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a69c : bv 32 := 0x0087e703.
Lemma F_1a69c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a784 : word) = Some W_1a69c.
Proof. vm_refl. Qed.
Lemma D_1a69c : decode_any W_1a69c = Some (Load SZ4 false 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6a0 : bv 32 := 0x00400693.
Lemma F_1a6a0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a788 : word) = Some W_1a6a0.
Proof. vm_refl. Qed.
Lemma D_1a6a0 : decode_any W_1a6a0 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6a4 : bv 32 := 0x00e6e463.
Lemma F_1a6a4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a78c : word) = Some W_1a6a4.
Proof. vm_refl. Qed.
Lemma D_1a6a4 : decode_any W_1a6a4 = Some (Branch BC_LTU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6ac : bv 32 := 0x0077c683.
Lemma F_1a6ac : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a794 : word) = Some W_1a6ac.
Proof. vm_refl. Qed.
Lemma D_1a6ac : decode_any W_1a6ac = Some (Load SZ1 false 13 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6b0 : bv 32 := 0x00068463.
Lemma F_1a6b0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a798 : word) = Some W_1a6b0.
Proof. vm_refl. Qed.
Lemma D_1a6b0 : decode_any W_1a6b0 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6b8 : bv 32 := 0x409606b3.
Lemma F_1a6b8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a7a0 : word) = Some W_1a6b8.
Proof. vm_refl. Qed.
Lemma D_1a6b8 : decode_any W_1a6b8 = Some (Op ALU_SUB 13 12 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6bc : bv 32 := 0x00e6f463.
Lemma F_1a6bc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a7a4 : word) = Some W_1a6bc.
Proof. vm_refl. Qed.
Lemma D_1a6bc : decode_any W_1a6bc = Some (Branch BC_GEU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6c4 : bv 32 := 0x40e606b3.
Lemma F_1a6c4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a7ac : word) = Some W_1a6c4.
Proof. vm_refl. Qed.
Lemma D_1a6c4 : decode_any W_1a6c4 = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6c8 : bv 32 := 0x0006c683.
Lemma F_1a6c8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a7b0 : word) = Some W_1a6c8.
Proof. vm_refl. Qed.
Lemma D_1a6c8 : decode_any W_1a6c8 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6cc : bv 32 := 0x00068463.
Lemma F_1a6cc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a7b4 : word) = Some W_1a6cc.
Proof. vm_refl. Qed.
Lemma D_1a6cc : decode_any W_1a6cc = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6d4 : bv 32 := 0x00064603.
Lemma F_1a6d4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a7bc : word) = Some W_1a6d4.
Proof. vm_refl. Qed.
Lemma D_1a6d4 : decode_any W_1a6d4 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6d8 : bv 32 := 0x00060463.
Lemma F_1a6d8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a7c0 : word) = Some W_1a6d8.
Proof. vm_refl. Qed.
Lemma D_1a6d8 : decode_any W_1a6d8 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a7d0 : bv 32 := 0x00f57593.
Lemma F_1a7d0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a8b8 : word) = Some W_1a7d0.
Proof. vm_refl. Qed.
Lemma D_1a7d0 : decode_any W_1a7d0 = Some (OpImm ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a7d4 : bv 32 := 0x00058463.
Lemma F_1a7d4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a8bc : word) = Some W_1a7d4.
Proof. vm_refl. Qed.
Lemma D_1a7d4 : decode_any W_1a7d4 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a7dc : bv 32 := 0xffc54603.
Lemma F_1a7dc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a8c4 : word) = Some W_1a7dc.
Proof. vm_refl. Qed.
Lemma D_1a7dc : decode_any W_1a7dc = Some (Load SZ1 false 12 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a7e0 : bv 32 := 0xffd54683.
Lemma F_1a7e0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a8c8 : word) = Some W_1a7e0.
Proof. vm_refl. Qed.
Lemma D_1a7e0 : decode_any W_1a7e0 = Some (Load SZ1 false 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a7e4 : bv 32 := 0xffe55583.
Lemma F_1a7e4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a8cc : word) = Some W_1a7e4.
Proof. vm_refl. Qed.
Lemma D_1a7e4 : decode_any W_1a7e4 = Some (Load SZ2 false 11 10 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a7e8 : bv 32 := 0x00060e63.
Lemma F_1a7e8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a8d0 : word) = Some W_1a7e8.
Proof. vm_refl. Qed.
Lemma D_1a7e8 : decode_any W_1a7e8 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a804 : bv 32 := 0x00459613.
Lemma F_1a804 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a8ec : word) = Some W_1a804.
Proof. vm_refl. Qed.
Lemma D_1a804 : decode_any W_1a804 = Some (ShiftImm ALU_SLL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a808 : bv 32 := 0x40c50633.
Lemma F_1a808 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a8f0 : word) = Some W_1a808.
Proof. vm_refl. Qed.
Lemma D_1a808 : decode_any W_1a808 = Some (Op ALU_SUB 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a80c : bv 32 := 0xff063503.
Lemma F_1a80c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a8f4 : word) = Some W_1a80c.
Proof. vm_refl. Qed.
Lemma D_1a80c : decode_any W_1a80c = Some (Load SZ8 true 10 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a810 : bv 32 := 0x01053703.
Lemma F_1a810 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a8f8 : word) = Some W_1a810.
Proof. vm_refl. Qed.
Lemma D_1a810 : decode_any W_1a810 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a814 : bv 32 := 0xff060613.
Lemma F_1a814 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a8fc : word) = Some W_1a814.
Proof. vm_refl. Qed.
Lemma D_1a814 : decode_any W_1a814 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a818 : bv 32 := 0x01f6f693.
Lemma F_1a818 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a900 : word) = Some W_1a818.
Proof. vm_refl. Qed.
Lemma D_1a818 : decode_any W_1a818 = Some (OpImm ALU_AND 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a81c : bv 32 := 0x00c70463.
Lemma F_1a81c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a904 : word) = Some W_1a81c.
Proof. vm_refl. Qed.
Lemma D_1a81c : decode_any W_1a81c = Some (Branch BC_EQ 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a824 : bv 32 := 0x02053603.
Lemma F_1a824 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a90c : word) = Some W_1a824.
Proof. vm_refl. Qed.
Lemma D_1a824 : decode_any W_1a824 = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a828 : bv 32 := 0x01f67713.
Lemma F_1a828 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a910 : word) = Some W_1a828.
Proof. vm_refl. Qed.
Lemma D_1a828 : decode_any W_1a828 = Some (OpImm ALU_AND 14 12 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a82c : bv 32 := 0x00d77463.
Lemma F_1a82c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a914 : word) = Some W_1a82c.
Proof. vm_refl. Qed.
Lemma D_1a82c : decode_any W_1a82c = Some (Branch BC_GEU 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a834 : bv 32 := 0x01852783.
Lemma F_1a834 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a91c : word) = Some W_1a834.
Proof. vm_refl. Qed.
Lemma D_1a834 : decode_any W_1a834 = Some (Load SZ4 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a838 : bv 32 := 0x00100713.
Lemma F_1a838 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a920 : word) = Some W_1a838.
Proof. vm_refl. Qed.
Lemma D_1a838 : decode_any W_1a838 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a83c : bv 32 := 0x00d7173b.
Lemma F_1a83c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a924 : word) = Some W_1a83c.
Proof. vm_refl. Qed.
Lemma D_1a83c : decode_any W_1a83c = Some (Op32 ALU_SLL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a840 : bv 32 := 0x00e7f7b3.
Lemma F_1a840 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a928 : word) = Some W_1a840.
Proof. vm_refl. Qed.
Lemma D_1a840 : decode_any W_1a840 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a844 : bv 32 := 0x00078463.
Lemma F_1a844 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a92c : word) = Some W_1a844.
Proof. vm_refl. Qed.
Lemma D_1a844 : decode_any W_1a844 = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a84c : bv 32 := 0x01c52783.
Lemma F_1a84c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a934 : word) = Some W_1a84c.
Proof. vm_refl. Qed.
Lemma D_1a84c : decode_any W_1a84c = Some (Load SZ4 true 15 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a850 : bv 32 := 0x00e7f733.
Lemma F_1a850 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a938 : word) = Some W_1a850.
Proof. vm_refl. Qed.
Lemma D_1a850 : decode_any W_1a850 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a854 : bv 32 := 0x00070463.
Lemma F_1a854 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a93c : word) = Some W_1a854.
Proof. vm_refl. Qed.
Lemma D_1a854 : decode_any W_1a854 = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a85c : bv 32 := 0xfffff737.
Lemma F_1a85c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a944 : word) = Some W_1a85c.
Proof. vm_refl. Qed.
Lemma D_1a85c : decode_any W_1a85c = Some (Lui 14 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a860 : bv 32 := 0x0007a797.
Lemma F_1a860 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a948 : word) = Some W_1a860.
Proof. vm_refl. Qed.
Lemma D_1a860 : decode_any W_1a860 = Some (Auipc 15 122, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a864 : bv 32 := 0x00e57733.
Lemma F_1a864 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a94c : word) = Some W_1a864.
Proof. vm_refl. Qed.
Lemma D_1a864 : decode_any W_1a864 = Some (Op ALU_AND 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a868 : bv 32 := 0x00073703.
Lemma F_1a868 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a950 : word) = Some W_1a868.
Proof. vm_refl. Qed.
Lemma D_1a868 : decode_any W_1a868 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a86c : bv 32 := 0xc087b783.
Lemma F_1a86c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a954 : word) = Some W_1a86c.
Proof. vm_refl. Qed.
Lemma D_1a86c : decode_any W_1a86c = Some (Load SZ8 true 15 15 3080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a870 : bv 32 := 0x00f70463.
Lemma F_1a870 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a958 : word) = Some W_1a870.
Proof. vm_refl. Qed.
Lemma D_1a870 : decode_any W_1a870 = Some (Branch BC_EQ 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a878 : bv 32 := 0x03461713.
Lemma F_1a878 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a960 : word) = Some W_1a878.
Proof. vm_refl. Qed.
Lemma D_1a878 : decode_any W_1a878 = Some (ShiftImm ALU_SLL 14 12 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a87c : bv 32 := 0x03a75713.
Lemma F_1a87c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a964 : word) = Some W_1a87c.
Proof. vm_refl. Qed.
Lemma D_1a87c : decode_any W_1a87c = Some (ShiftImm ALU_SRL 14 14 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a880 : bv 32 := 0x02f00793.
Lemma F_1a880 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a968 : word) = Some W_1a880.
Proof. vm_refl. Qed.
Lemma D_1a880 : decode_any W_1a880 = Some (OpImm ALU_ADD 15 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a884 : bv 32 := 0x02e7ea63.
Lemma F_1a884 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a96c : word) = Some W_1a884.
Proof. vm_refl. Qed.
Lemma D_1a884 : decode_any W_1a884 = Some (Branch BC_LTU 15 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a888 : bv 32 := 0x00171713.
Lemma F_1a888 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a970 : word) = Some W_1a888.
Proof. vm_refl. Qed.
Lemma D_1a888 : decode_any W_1a888 = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a88c : bv 32 := 0xffff8797.
Lemma F_1a88c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a974 : word) = Some W_1a88c.
Proof. vm_refl. Qed.
Lemma D_1a88c : decode_any W_1a88c = Some (Auipc 15 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a890 : bv 32 := 0xae878793.
Lemma F_1a890 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a978 : word) = Some W_1a890.
Proof. vm_refl. Qed.
Lemma D_1a890 : decode_any W_1a890 = Some (OpImm ALU_ADD 15 15 2792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a894 : bv 32 := 0x00e78733.
Lemma F_1a894 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a97c : word) = Some W_1a894.
Proof. vm_refl. Qed.
Lemma D_1a894 : decode_any W_1a894 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a898 : bv 32 := 0x00075703.
Lemma F_1a898 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a980 : word) = Some W_1a898.
Proof. vm_refl. Qed.
Lemma D_1a898 : decode_any W_1a898 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a89c : bv 32 := 0x02d707b3.
Lemma F_1a89c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a984 : word) = Some W_1a89c.
Proof. vm_refl. Qed.
Lemma D_1a89c : decode_any W_1a89c = Some (Mul M_MUL 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8a0 : bv 32 := 0x00f5f463.
Lemma F_1a8a0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a988 : word) = Some W_1a8a0.
Proof. vm_refl. Qed.
Lemma D_1a8a0 : decode_any W_1a8a0 = Some (Branch BC_GEU 11 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8a8 : bv 32 := 0x00168693.
Lemma F_1a8a8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a990 : word) = Some W_1a8a8.
Proof. vm_refl. Qed.
Lemma D_1a8a8 : decode_any W_1a8a8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8ac : bv 32 := 0x02e686b3.
Lemma F_1a8ac : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a994 : word) = Some W_1a8ac.
Proof. vm_refl. Qed.
Lemma D_1a8ac : decode_any W_1a8ac = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8b0 : bv 32 := 0x00d5f863.
Lemma F_1a8b0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a998 : word) = Some W_1a8b0.
Proof. vm_refl. Qed.
Lemma D_1a8b0 : decode_any W_1a8b0 = Some (Branch BC_GEU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8b4 : bv 32 := 0x0100006f.
Lemma F_1a8b4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a99c : word) = Some W_1a8b4.
Proof. vm_refl. Qed.
Lemma D_1a8b4 : decode_any W_1a8b4 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8b8 : bv 32 := 0x03f00693.
Lemma F_1a8b8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a9a0 : word) = Some W_1a8b8.
Proof. vm_refl. Qed.
Lemma D_1a8b8 : decode_any W_1a8b8 = Some (OpImm ALU_ADD 13 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8bc : bv 32 := 0x00d70463.
Lemma F_1a8bc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a9a4 : word) = Some W_1a8bc.
Proof. vm_refl. Qed.
Lemma D_1a8bc : decode_any W_1a8bc = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8c4 : bv 32 := 0x00c65613.
Lemma F_1a8c4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a9ac : word) = Some W_1a8c4.
Proof. vm_refl. Qed.
Lemma D_1a8c4 : decode_any W_1a8c4 = Some (ShiftImm ALU_SRL 12 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8c8 : bv 32 := 0x00060a63.
Lemma F_1a8c8 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a9b0 : word) = Some W_1a8c8.
Proof. vm_refl. Qed.
Lemma D_1a8c8 : decode_any W_1a8c8 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8cc : bv 32 := 0x00861613.
Lemma F_1a8cc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a9b4 : word) = Some W_1a8cc.
Proof. vm_refl. Qed.
Lemma D_1a8cc : decode_any W_1a8cc = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8d0 : bv 32 := 0xfff60613.
Lemma F_1a8d0 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a9b8 : word) = Some W_1a8d0.
Proof. vm_refl. Qed.
Lemma D_1a8d0 : decode_any W_1a8d0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8d4 : bv 32 := 0x00b67463.
Lemma F_1a8d4 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a9bc : word) = Some W_1a8d4.
Proof. vm_refl. Qed.
Lemma D_1a8d4 : decode_any W_1a8d4 = Some (Branch BC_GEU 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8dc : bv 32 := 0x00008067.
Lemma F_1a8dc : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1a9c4 : word) = Some W_1a8dc.
Proof. vm_refl. Qed.
Lemma D_1a8dc : decode_any W_1a8dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ac60 : bv 32 := 0x00072503.
Lemma F_1ac60 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1ad48 : word) = Some W_1ac60.
Proof. vm_refl. Qed.
Lemma D_1ac60 : decode_any W_1ac60 = Some (Load SZ4 true 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ac64 : bv 32 := 0x00b56633.
Lemma F_1ac64 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1ad4c : word) = Some W_1ac64.
Proof. vm_refl. Qed.
Lemma D_1ac64 : decode_any W_1ac64 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ac68 : bv 32 := 0x160726af.
Lemma F_1ac68 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1ad50 : word) = Some W_1ac68.
Proof. vm_refl. Qed.
Lemma D_1ac68 : decode_any W_1ac68 = Some (Lr AW true true 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ac6c : bv 32 := 0x00a69663.
Lemma F_1ac6c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1ad54 : word) = Some W_1ac6c.
Proof. vm_refl. Qed.
Lemma D_1ac6c : decode_any W_1ac6c = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ac70 : bv 32 := 0x1ec727af.
Lemma F_1ac70 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1ad58 : word) = Some W_1ac70.
Proof. vm_refl. Qed.
Lemma D_1ac70 : decode_any W_1ac70 = Some (Sc AW true true 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ac74 : bv 32 := 0xfe079ae3.
Lemma F_1ac74 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1ad5c : word) = Some W_1ac74.
Proof. vm_refl. Qed.
Lemma D_1ac74 : decode_any W_1ac74 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ac78 : bv 32 := 0x0006869b.
Lemma F_1ac78 : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1ad60 : word) = Some W_1ac78.
Proof. vm_refl. Qed.
Lemma D_1ac78 : decode_any W_1ac78 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ac7c : bv 32 := 0xfea692e3.
Lemma F_1ac7c : fetch_word TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1ad64 : word) = Some W_1ac7c.
Proof. vm_refl. Qed.
Lemma D_1ac7c : decode_any W_1ac7c = Some (Branch BC_NE 13 10 8164, 4%Z).
Proof. vm_refl. Qed.
