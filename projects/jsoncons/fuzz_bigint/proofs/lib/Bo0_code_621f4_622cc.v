(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_621f4 : bv 32 := 0xfb010113.
Lemma F_621f4 : fetch_word AsanUbsan.M.loaded_segments (0x621f4 : word) = Some W_621f4.
Proof. vm_refl. Qed.
Lemma D_621f4 : decode_any W_621f4 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_621f8 : bv 32 := 0x04113423.
Lemma F_621f8 : fetch_word AsanUbsan.M.loaded_segments (0x621f8 : word) = Some W_621f8.
Proof. vm_refl. Qed.
Lemma D_621f8 : decode_any W_621f8 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_621fc : bv 32 := 0x04813023.
Lemma F_621fc : fetch_word AsanUbsan.M.loaded_segments (0x621fc : word) = Some W_621fc.
Proof. vm_refl. Qed.
Lemma D_621fc : decode_any W_621fc = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_62200 : bv 32 := 0x00074517.
Lemma F_62200 : fetch_word AsanUbsan.M.loaded_segments (0x62200 : word) = Some W_62200.
Proof. vm_refl. Qed.
Lemma D_62200 : decode_any W_62200 = Some (Auipc 10 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_62204 : bv 32 := 0x30853503.
Lemma F_62204 : fetch_word AsanUbsan.M.loaded_segments (0x62204 : word) = Some W_62204.
Proof. vm_refl. Qed.
Lemma D_62204 : decode_any W_62204 = Some (Load SZ8 true 10 10 776, 4%Z).
Proof. vm_refl. Qed.

Definition W_62208 : bv 32 := 0x0a051463.
Lemma F_62208 : fetch_word AsanUbsan.M.loaded_segments (0x62208 : word) = Some W_62208.
Proof. vm_refl. Qed.
Lemma D_62208 : decode_any W_62208 = Some (Branch BC_NE 10 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6220c : bv 32 := 0xfffae517.
Lemma F_6220c : fetch_word AsanUbsan.M.loaded_segments (0x6220c : word) = Some W_6220c.
Proof. vm_refl. Qed.
Lemma D_6220c : decode_any W_6220c = Some (Auipc 10 1048494, 4%Z).
Proof. vm_refl. Qed.

Definition W_62210 : bv 32 := 0x1fc53403.
Lemma F_62210 : fetch_word AsanUbsan.M.loaded_segments (0x62210 : word) = Some W_62210.
Proof. vm_refl. Qed.
Lemma D_62210 : decode_any W_62210 = Some (Load SZ8 true 8 10 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_62214 : bv 32 := 0x02813423.
Lemma F_62214 : fetch_word AsanUbsan.M.loaded_segments (0x62214 : word) = Some W_62214.
Proof. vm_refl. Qed.
Lemma D_62214 : decode_any W_62214 = Some (Store SZ8 2 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_62218 : bv 32 := 0x02813823.
Lemma F_62218 : fetch_word AsanUbsan.M.loaded_segments (0x62218 : word) = Some W_62218.
Proof. vm_refl. Qed.
Lemma D_62218 : decode_any W_62218 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6221c : bv 32 := 0x02813c23.
Lemma F_6221c : fetch_word AsanUbsan.M.loaded_segments (0x6221c : word) = Some W_6221c.
Proof. vm_refl. Qed.
Lemma D_6221c : decode_any W_6221c = Some (Store SZ8 2 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_62220 : bv 32 := 0x02810593.
Lemma F_62220 : fetch_word AsanUbsan.M.loaded_segments (0x62220 : word) = Some W_62220.
Proof. vm_refl. Qed.
Lemma D_62220 : decode_any W_62220 = Some (OpImm ALU_ADD 11 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_62224 : bv 32 := 0x00000513.
Lemma F_62224 : fetch_word AsanUbsan.M.loaded_segments (0x62224 : word) = Some W_62224.
Proof. vm_refl. Qed.
Lemma D_62224 : decode_any W_62224 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_62228 : bv 32 := 0xc9deb0ef.
Lemma F_62228 : fetch_word AsanUbsan.M.loaded_segments (0x62228 : word) = Some W_62228.
Proof. vm_refl. Qed.
Lemma D_62228 : decode_any W_62228 = Some (Jal 1 2014364, 4%Z).
Proof. vm_refl. Qed.

Definition W_6222c : bv 32 := 0x08051c63.
Lemma F_6222c : fetch_word AsanUbsan.M.loaded_segments (0x6222c : word) = Some W_6222c.
Proof. vm_refl. Qed.
Lemma D_6222c : decode_any W_6222c = Some (Branch BC_NE 10 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_62230 : bv 32 := 0x03012503.
Lemma F_62230 : fetch_word AsanUbsan.M.loaded_segments (0x62230 : word) = Some W_62230.
Proof. vm_refl. Qed.
Lemma D_62230 : decode_any W_62230 = Some (Load SZ4 true 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_62234 : bv 32 := 0x00200593.
Lemma F_62234 : fetch_word AsanUbsan.M.loaded_segments (0x62234 : word) = Some W_62234.
Proof. vm_refl. Qed.
Lemma D_62234 : decode_any W_62234 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_62238 : bv 32 := 0x06b50c63.
Lemma F_62238 : fetch_word AsanUbsan.M.loaded_segments (0x62238 : word) = Some W_62238.
Proof. vm_refl. Qed.
Lemma D_62238 : decode_any W_62238 = Some (Branch BC_EQ 10 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_6223c : bv 32 := 0x02813503.
Lemma F_6223c : fetch_word AsanUbsan.M.loaded_segments (0x6223c : word) = Some W_6223c.
Proof. vm_refl. Qed.
Lemma D_6223c : decode_any W_6223c = Some (Load SZ8 true 10 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_62240 : bv 32 := 0x03813583.
Lemma F_62240 : fetch_word AsanUbsan.M.loaded_segments (0x62240 : word) = Some W_62240.
Proof. vm_refl. Qed.
Lemma D_62240 : decode_any W_62240 = Some (Load SZ8 true 11 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_62244 : bv 32 := 0x00b505b3.
Lemma F_62244 : fetch_word AsanUbsan.M.loaded_segments (0x62244 : word) = Some W_62244.
Proof. vm_refl. Qed.
Lemma D_62244 : decode_any W_62244 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_62248 : bv 32 := 0xfffbd617.
Lemma F_62248 : fetch_word AsanUbsan.M.loaded_segments (0x62248 : word) = Some W_62248.
Proof. vm_refl. Qed.
Lemma D_62248 : decode_any W_62248 = Some (Auipc 12 1048509, 4%Z).
Proof. vm_refl. Qed.

Definition W_6224c : bv 32 := 0x49e60613.
Lemma F_6224c : fetch_word AsanUbsan.M.loaded_segments (0x6224c : word) = Some W_6224c.
Proof. vm_refl. Qed.
Lemma D_6224c : decode_any W_6224c = Some (OpImm ALU_ADD 12 12 1182, 4%Z).
Proof. vm_refl. Qed.

Definition W_62250 : bv 32 := 0x0b4050ef.
Lemma F_62250 : fetch_word AsanUbsan.M.loaded_segments (0x62250 : word) = Some W_62250.
Proof. vm_refl. Qed.
Lemma D_62250 : decode_any W_62250 = Some (Jal 1 20660, 4%Z).
Proof. vm_refl. Qed.

Definition W_62254 : bv 32 := 0x03012503.
Lemma F_62254 : fetch_word AsanUbsan.M.loaded_segments (0x62254 : word) = Some W_62254.
Proof. vm_refl. Qed.
Lemma D_62254 : decode_any W_62254 = Some (Load SZ4 true 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_62258 : bv 32 := 0x00100593.
Lemma F_62258 : fetch_word AsanUbsan.M.loaded_segments (0x62258 : word) = Some W_62258.
Proof. vm_refl. Qed.
Lemma D_62258 : decode_any W_62258 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6225c : bv 32 := 0x04b51a63.
Lemma F_6225c : fetch_word AsanUbsan.M.loaded_segments (0x6225c : word) = Some W_6225c.
Proof. vm_refl. Qed.
Lemma D_6225c : decode_any W_6225c = Some (Branch BC_NE 10 11 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_62260 : bv 32 := 0x02813023.
Lemma F_62260 : fetch_word AsanUbsan.M.loaded_segments (0x62260 : word) = Some W_62260.
Proof. vm_refl. Qed.
Lemma D_62260 : decode_any W_62260 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_62264 : bv 32 := 0x00813c23.
Lemma F_62264 : fetch_word AsanUbsan.M.loaded_segments (0x62264 : word) = Some W_62264.
Proof. vm_refl. Qed.
Lemma D_62264 : decode_any W_62264 = Some (Store SZ8 2 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_62268 : bv 32 := 0x00813823.
Lemma F_62268 : fetch_word AsanUbsan.M.loaded_segments (0x62268 : word) = Some W_62268.
Proof. vm_refl. Qed.
Lemma D_62268 : decode_any W_62268 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6226c : bv 32 := 0x00813423.
Lemma F_6226c : fetch_word AsanUbsan.M.loaded_segments (0x6226c : word) = Some W_6226c.
Proof. vm_refl. Qed.
Lemma D_6226c : decode_any W_6226c = Some (Store SZ8 2 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_62270 : bv 32 := 0x02010593.
Lemma F_62270 : fetch_word AsanUbsan.M.loaded_segments (0x62270 : word) = Some W_62270.
Proof. vm_refl. Qed.
Lemma D_62270 : decode_any W_62270 = Some (OpImm ALU_ADD 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_62274 : bv 32 := 0x01810613.
Lemma F_62274 : fetch_word AsanUbsan.M.loaded_segments (0x62274 : word) = Some W_62274.
Proof. vm_refl. Qed.
Lemma D_62274 : decode_any W_62274 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_62278 : bv 32 := 0x01010693.
Lemma F_62278 : fetch_word AsanUbsan.M.loaded_segments (0x62278 : word) = Some W_62278.
Proof. vm_refl. Qed.
Lemma D_62278 : decode_any W_62278 = Some (OpImm ALU_ADD 13 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6227c : bv 32 := 0x00810713.
Lemma F_6227c : fetch_word AsanUbsan.M.loaded_segments (0x6227c : word) = Some W_6227c.
Proof. vm_refl. Qed.
Lemma D_6227c : decode_any W_6227c = Some (OpImm ALU_ADD 14 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_62280 : bv 32 := 0x00000513.
Lemma F_62280 : fetch_word AsanUbsan.M.loaded_segments (0x62280 : word) = Some W_62280.
Proof. vm_refl. Qed.
Lemma D_62280 : decode_any W_62280 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_62284 : bv 32 := 0x34c180ef.
Lemma F_62284 : fetch_word AsanUbsan.M.loaded_segments (0x62284 : word) = Some W_62284.
Proof. vm_refl. Qed.
Lemma D_62284 : decode_any W_62284 = Some (Jal 1 99148, 4%Z).
Proof. vm_refl. Qed.

Definition W_62288 : bv 32 := 0x02013503.
Lemma F_62288 : fetch_word AsanUbsan.M.loaded_segments (0x62288 : word) = Some W_62288.
Proof. vm_refl. Qed.
Lemma D_62288 : decode_any W_62288 = Some (Load SZ8 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6228c : bv 32 := 0x01813583.
Lemma F_6228c : fetch_word AsanUbsan.M.loaded_segments (0x6228c : word) = Some W_6228c.
Proof. vm_refl. Qed.
Lemma D_6228c : decode_any W_6228c = Some (Load SZ8 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_62290 : bv 32 := 0xfffb9617.
Lemma F_62290 : fetch_word AsanUbsan.M.loaded_segments (0x62290 : word) = Some W_62290.
Proof. vm_refl. Qed.
Lemma D_62290 : decode_any W_62290 = Some (Auipc 12 1048505, 4%Z).
Proof. vm_refl. Qed.

Definition W_62294 : bv 32 := 0x80660613.
Lemma F_62294 : fetch_word AsanUbsan.M.loaded_segments (0x62294 : word) = Some W_62294.
Proof. vm_refl. Qed.
Lemma D_62294 : decode_any W_62294 = Some (OpImm ALU_ADD 12 12 2054, 4%Z).
Proof. vm_refl. Qed.

Definition W_62298 : bv 32 := 0x06c050ef.
Lemma F_62298 : fetch_word AsanUbsan.M.loaded_segments (0x62298 : word) = Some W_62298.
Proof. vm_refl. Qed.
Lemma D_62298 : decode_any W_62298 = Some (Jal 1 20588, 4%Z).
Proof. vm_refl. Qed.

Definition W_6229c : bv 32 := 0x00100513.
Lemma F_6229c : fetch_word AsanUbsan.M.loaded_segments (0x6229c : word) = Some W_6229c.
Proof. vm_refl. Qed.
Lemma D_6229c : decode_any W_6229c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_622a0 : bv 32 := 0x04813083.
Lemma F_622a0 : fetch_word AsanUbsan.M.loaded_segments (0x622a0 : word) = Some W_622a0.
Proof. vm_refl. Qed.
Lemma D_622a0 : decode_any W_622a0 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_622a4 : bv 32 := 0x04013403.
Lemma F_622a4 : fetch_word AsanUbsan.M.loaded_segments (0x622a4 : word) = Some W_622a4.
Proof. vm_refl. Qed.
Lemma D_622a4 : decode_any W_622a4 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_622a8 : bv 32 := 0x05010113.
Lemma F_622a8 : fetch_word AsanUbsan.M.loaded_segments (0x622a8 : word) = Some W_622a8.
Proof. vm_refl. Qed.
Lemma D_622a8 : decode_any W_622a8 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_622ac : bv 32 := 0x00008067.
Lemma F_622ac : fetch_word AsanUbsan.M.loaded_segments (0x622ac : word) = Some W_622ac.
Proof. vm_refl. Qed.
Lemma D_622ac : decode_any W_622ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_622b0 : bv 32 := 0x00000513.
Lemma F_622b0 : fetch_word AsanUbsan.M.loaded_segments (0x622b0 : word) = Some W_622b0.
Proof. vm_refl. Qed.
Lemma D_622b0 : decode_any W_622b0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_622b4 : bv 32 := 0x04813083.
Lemma F_622b4 : fetch_word AsanUbsan.M.loaded_segments (0x622b4 : word) = Some W_622b4.
Proof. vm_refl. Qed.
Lemma D_622b4 : decode_any W_622b4 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_622b8 : bv 32 := 0x04013403.
Lemma F_622b8 : fetch_word AsanUbsan.M.loaded_segments (0x622b8 : word) = Some W_622b8.
Proof. vm_refl. Qed.
Lemma D_622b8 : decode_any W_622b8 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_622bc : bv 32 := 0x05010113.
Lemma F_622bc : fetch_word AsanUbsan.M.loaded_segments (0x622bc : word) = Some W_622bc.
Proof. vm_refl. Qed.
Lemma D_622bc : decode_any W_622bc = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_622c0 : bv 32 := 0x00008067.
Lemma F_622c0 : fetch_word AsanUbsan.M.loaded_segments (0x622c0 : word) = Some W_622c0.
Proof. vm_refl. Qed.
Lemma D_622c0 : decode_any W_622c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_622c4 : bv 32 := 0x00050713.
Lemma F_622c4 : fetch_word AsanUbsan.M.loaded_segments (0x622c4 : word) = Some W_622c4.
Proof. vm_refl. Qed.
Lemma D_622c4 : decode_any W_622c4 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_622c8 : bv 32 := 0xfffb9517.
Lemma F_622c8 : fetch_word AsanUbsan.M.loaded_segments (0x622c8 : word) = Some W_622c8.
Proof. vm_refl. Qed.
Lemma D_622c8 : decode_any W_622c8 = Some (Auipc 10 1048505, 4%Z).
Proof. vm_refl. Qed.
