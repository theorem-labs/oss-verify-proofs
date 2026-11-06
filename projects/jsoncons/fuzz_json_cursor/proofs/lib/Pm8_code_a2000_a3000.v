(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a213c : bv 32 := 0xfc010113.
Lemma F_a213c : fetch_word Asan.M.loaded_segments (0xa218c : word) = Some W_a213c.
Proof. vm_refl. Qed.
Lemma D_a213c : decode_any W_a213c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2140 : bv 32 := 0x02113c23.
Lemma F_a2140 : fetch_word Asan.M.loaded_segments (0xa2190 : word) = Some W_a2140.
Proof. vm_refl. Qed.
Lemma D_a2140 : decode_any W_a2140 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2144 : bv 32 := 0x02813823.
Lemma F_a2144 : fetch_word Asan.M.loaded_segments (0xa2194 : word) = Some W_a2144.
Proof. vm_refl. Qed.
Lemma D_a2144 : decode_any W_a2144 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2148 : bv 32 := 0x02913423.
Lemma F_a2148 : fetch_word Asan.M.loaded_segments (0xa2198 : word) = Some W_a2148.
Proof. vm_refl. Qed.
Lemma D_a2148 : decode_any W_a2148 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a214c : bv 32 := 0x03213023.
Lemma F_a214c : fetch_word Asan.M.loaded_segments (0xa219c : word) = Some W_a214c.
Proof. vm_refl. Qed.
Lemma D_a214c : decode_any W_a214c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2150 : bv 32 := 0x01313c23.
Lemma F_a2150 : fetch_word Asan.M.loaded_segments (0xa21a0 : word) = Some W_a2150.
Proof. vm_refl. Qed.
Lemma D_a2150 : decode_any W_a2150 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2154 : bv 32 := 0x01413823.
Lemma F_a2154 : fetch_word Asan.M.loaded_segments (0xa21a4 : word) = Some W_a2154.
Proof. vm_refl. Qed.
Lemma D_a2154 : decode_any W_a2154 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2158 : bv 32 := 0x01513423.
Lemma F_a2158 : fetch_word Asan.M.loaded_segments (0xa21a8 : word) = Some W_a2158.
Proof. vm_refl. Qed.
Lemma D_a2158 : decode_any W_a2158 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a215c : bv 32 := 0x00058413.
Lemma F_a215c : fetch_word Asan.M.loaded_segments (0xa21ac : word) = Some W_a215c.
Proof. vm_refl. Qed.
Lemma D_a215c : decode_any W_a215c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2160 : bv 32 := 0x0015b593.
Lemma F_a2160 : fetch_word Asan.M.loaded_segments (0xa21b0 : word) = Some W_a2160.
Proof. vm_refl. Qed.
Lemma D_a2160 : decode_any W_a2160 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2164 : bv 32 := 0x7ff50293.
Lemma F_a2164 : fetch_word Asan.M.loaded_segments (0xa21b4 : word) = Some W_a2164.
Proof. vm_refl. Qed.
Lemma D_a2164 : decode_any W_a2164 = Some (OpImm ALU_ADD 5 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2168 : bv 32 := 0xfff58593.
Lemma F_a2168 : fetch_word Asan.M.loaded_segments (0xa21b8 : word) = Some W_a2168.
Proof. vm_refl. Qed.
Lemma D_a2168 : decode_any W_a2168 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a216c : bv 32 := 0x00d5f333.
Lemma F_a216c : fetch_word Asan.M.loaded_segments (0xa21bc : word) = Some W_a216c.
Proof. vm_refl. Qed.
Lemma D_a216c : decode_any W_a216c = Some (Op ALU_AND 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2170 : bv 32 := 0x00100593.
Lemma F_a2170 : fetch_word Asan.M.loaded_segments (0xa21c0 : word) = Some W_a2170.
Proof. vm_refl. Qed.
Lemma D_a2170 : decode_any W_a2170 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2174 : bv 32 := 0x0062b4a3.
Lemma F_a2174 : fetch_word Asan.M.loaded_segments (0xa21c4 : word) = Some W_a2174.
Proof. vm_refl. Qed.
Lemma D_a2174 : decode_any W_a2174 = Some (Store SZ8 5 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2178 : bv 32 := 0x00b40863.
Lemma F_a2178 : fetch_word Asan.M.loaded_segments (0xa21c8 : word) = Some W_a2178.
Proof. vm_refl. Qed.
Lemma D_a2178 : decode_any W_a2178 = Some (Branch BC_EQ 8 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a217c : bv 32 := 0x02041c63.
Lemma F_a217c : fetch_word Asan.M.loaded_segments (0xa21cc : word) = Some W_a217c.
Proof. vm_refl. Qed.
Lemma D_a217c : decode_any W_a217c = Some (Branch BC_NE 8 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a21b4 : bv 32 := 0x06089463.
Lemma F_a21b4 : fetch_word Asan.M.loaded_segments (0xa2204 : word) = Some W_a21b4.
Proof. vm_refl. Qed.
Lemma D_a21b4 : decode_any W_a21b4 = Some (Branch BC_NE 17 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a221c : bv 32 := 0x00060593.
Lemma F_a221c : fetch_word Asan.M.loaded_segments (0xa226c : word) = Some W_a221c.
Proof. vm_refl. Qed.
Lemma D_a221c : decode_any W_a221c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2220 : bv 32 := 0x00068613.
Lemma F_a2220 : fetch_word Asan.M.loaded_segments (0xa2270 : word) = Some W_a2220.
Proof. vm_refl. Qed.
Lemma D_a2220 : decode_any W_a2220 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2224 : bv 32 := 0x00078693.
Lemma F_a2224 : fetch_word Asan.M.loaded_segments (0xa2274 : word) = Some W_a2224.
Proof. vm_refl. Qed.
Lemma D_a2224 : decode_any W_a2224 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2228 : bv 32 := 0x00080713.
Lemma F_a2228 : fetch_word Asan.M.loaded_segments (0xa2278 : word) = Some W_a2228.
Proof. vm_refl. Qed.
Lemma D_a2228 : decode_any W_a2228 = Some (OpImm ALU_ADD 14 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a222c : bv 32 := 0x00040793.
Lemma F_a222c : fetch_word Asan.M.loaded_segments (0xa227c : word) = Some W_a222c.
Proof. vm_refl. Qed.
Lemma D_a222c : decode_any W_a222c = Some (OpImm ALU_ADD 15 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2230 : bv 32 := 0x03813083.
Lemma F_a2230 : fetch_word Asan.M.loaded_segments (0xa2280 : word) = Some W_a2230.
Proof. vm_refl. Qed.
Lemma D_a2230 : decode_any W_a2230 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2234 : bv 32 := 0x03013403.
Lemma F_a2234 : fetch_word Asan.M.loaded_segments (0xa2284 : word) = Some W_a2234.
Proof. vm_refl. Qed.
Lemma D_a2234 : decode_any W_a2234 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2238 : bv 32 := 0x02813483.
Lemma F_a2238 : fetch_word Asan.M.loaded_segments (0xa2288 : word) = Some W_a2238.
Proof. vm_refl. Qed.
Lemma D_a2238 : decode_any W_a2238 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a223c : bv 32 := 0x02013903.
Lemma F_a223c : fetch_word Asan.M.loaded_segments (0xa228c : word) = Some W_a223c.
Proof. vm_refl. Qed.
Lemma D_a223c : decode_any W_a223c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2240 : bv 32 := 0x01813983.
Lemma F_a2240 : fetch_word Asan.M.loaded_segments (0xa2290 : word) = Some W_a2240.
Proof. vm_refl. Qed.
Lemma D_a2240 : decode_any W_a2240 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2244 : bv 32 := 0x01013a03.
Lemma F_a2244 : fetch_word Asan.M.loaded_segments (0xa2294 : word) = Some W_a2244.
Proof. vm_refl. Qed.
Lemma D_a2244 : decode_any W_a2244 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2248 : bv 32 := 0x00813a83.
Lemma F_a2248 : fetch_word Asan.M.loaded_segments (0xa2298 : word) = Some W_a2248.
Proof. vm_refl. Qed.
Lemma D_a2248 : decode_any W_a2248 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a224c : bv 32 := 0x04010113.
Lemma F_a224c : fetch_word Asan.M.loaded_segments (0xa229c : word) = Some W_a224c.
Proof. vm_refl. Qed.
Lemma D_a224c : decode_any W_a224c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2250 : bv 32 := 0x891ff06f.
Lemma F_a2250 : fetch_word Asan.M.loaded_segments (0xa22a0 : word) = Some W_a2250.
Proof. vm_refl. Qed.
Lemma D_a2250 : decode_any W_a2250 = Some (Jal 0 2095248, 4%Z).
Proof. vm_refl. Qed.

