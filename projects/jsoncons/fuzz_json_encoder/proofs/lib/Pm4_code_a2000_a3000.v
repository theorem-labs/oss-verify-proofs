(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a2238 : bv 32 := 0xfe010113.
Lemma F_a2238 : fetch_word Asan.M.loaded_segments (0xa2288 : word) = Some W_a2238.
Proof. vm_refl. Qed.
Lemma D_a2238 : decode_any W_a2238 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a223c : bv 32 := 0x00113c23.
Lemma F_a223c : fetch_word Asan.M.loaded_segments (0xa228c : word) = Some W_a223c.
Proof. vm_refl. Qed.
Lemma D_a223c : decode_any W_a223c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2240 : bv 32 := 0x00813823.
Lemma F_a2240 : fetch_word Asan.M.loaded_segments (0xa2290 : word) = Some W_a2240.
Proof. vm_refl. Qed.
Lemma D_a2240 : decode_any W_a2240 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2244 : bv 32 := 0x00060593.
Lemma F_a2244 : fetch_word Asan.M.loaded_segments (0xa2294 : word) = Some W_a2244.
Proof. vm_refl. Qed.
Lemma D_a2244 : decode_any W_a2244 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2248 : bv 32 := 0x00050413.
Lemma F_a2248 : fetch_word Asan.M.loaded_segments (0xa2298 : word) = Some W_a2248.
Proof. vm_refl. Qed.
Lemma D_a2248 : decode_any W_a2248 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a224c : bv 32 := 0x00d53023.
Lemma F_a224c : fetch_word Asan.M.loaded_segments (0xa229c : word) = Some W_a224c.
Proof. vm_refl. Qed.
Lemma D_a224c : decode_any W_a224c = Some (Store SZ8 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2250 : bv 32 := 0x00013423.
Lemma F_a2250 : fetch_word Asan.M.loaded_segments (0xa22a0 : word) = Some W_a2250.
Proof. vm_refl. Qed.
Lemma D_a2250 : decode_any W_a2250 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2254 : bv 32 := 0x0019a517.
Lemma F_a2254 : fetch_word Asan.M.loaded_segments (0xa22a4 : word) = Some W_a2254.
Proof. vm_refl. Qed.
Lemma D_a2254 : decode_any W_a2254 = Some (Auipc 10 410, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2258 : bv 32 := 0xb2450513.
Lemma F_a2258 : fetch_word Asan.M.loaded_segments (0xa22a8 : word) = Some W_a2258.
Proof. vm_refl. Qed.
Lemma D_a2258 : decode_any W_a2258 = Some (OpImm ALU_ADD 10 10 2852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a225c : bv 32 := 0x00810613.
Lemma F_a225c : fetch_word Asan.M.loaded_segments (0xa22ac : word) = Some W_a225c.
Proof. vm_refl. Qed.
Lemma D_a225c : decode_any W_a225c = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2260 : bv 32 := 0xcc5fd0ef.
Lemma F_a2260 : fetch_word Asan.M.loaded_segments (0xa22b0 : word) = Some W_a2260.
Proof. vm_refl. Qed.
Lemma D_a2260 : decode_any W_a2260 = Some (Jal 1 2088132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2264 : bv 32 := 0x00813583.
Lemma F_a2264 : fetch_word Asan.M.loaded_segments (0xa22b4 : word) = Some W_a2264.
Proof. vm_refl. Qed.
Lemma D_a2264 : decode_any W_a2264 = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2268 : bv 32 := 0x00a42623.
Lemma F_a2268 : fetch_word Asan.M.loaded_segments (0xa22b8 : word) = Some W_a2268.
Proof. vm_refl. Qed.
Lemma D_a2268 : decode_any W_a2268 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a226c : bv 32 := 0x00059a63.
Lemma F_a226c : fetch_word Asan.M.loaded_segments (0xa22bc : word) = Some W_a226c.
Proof. vm_refl. Qed.
Lemma D_a226c : decode_any W_a226c = Some (Branch BC_NE 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2270 : bv 32 := 0x01813083.
Lemma F_a2270 : fetch_word Asan.M.loaded_segments (0xa22c0 : word) = Some W_a2270.
Proof. vm_refl. Qed.
Lemma D_a2270 : decode_any W_a2270 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2274 : bv 32 := 0x01013403.
Lemma F_a2274 : fetch_word Asan.M.loaded_segments (0xa22c4 : word) = Some W_a2274.
Proof. vm_refl. Qed.
Lemma D_a2274 : decode_any W_a2274 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2278 : bv 32 := 0x02010113.
Lemma F_a2278 : fetch_word Asan.M.loaded_segments (0xa22c8 : word) = Some W_a2278.
Proof. vm_refl. Qed.
Lemma D_a2278 : decode_any W_a2278 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a227c : bv 32 := 0x00008067.
Lemma F_a227c : fetch_word Asan.M.loaded_segments (0xa22cc : word) = Some W_a227c.
Proof. vm_refl. Qed.
Lemma D_a227c : decode_any W_a227c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2520 : bv 32 := 0x00058613.
Lemma F_a2520 : fetch_word Asan.M.loaded_segments (0xa2570 : word) = Some W_a2520.
Proof. vm_refl. Qed.
Lemma D_a2520 : decode_any W_a2520 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2524 : bv 32 := 0x001aa597.
Lemma F_a2524 : fetch_word Asan.M.loaded_segments (0xa2574 : word) = Some W_a2524.
Proof. vm_refl. Qed.
Lemma D_a2524 : decode_any W_a2524 = Some (Auipc 11 426, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2528 : bv 32 := 0x86458593.
Lemma F_a2528 : fetch_word Asan.M.loaded_segments (0xa2578 : word) = Some W_a2528.
Proof. vm_refl. Qed.
Lemma D_a2528 : decode_any W_a2528 = Some (OpImm ALU_ADD 11 11 2148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a252c : bv 32 := 0x00050693.
Lemma F_a252c : fetch_word Asan.M.loaded_segments (0xa257c : word) = Some W_a252c.
Proof. vm_refl. Qed.
Lemma D_a252c : decode_any W_a252c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2530 : bv 32 := 0x00058513.
Lemma F_a2530 : fetch_word Asan.M.loaded_segments (0xa2580 : word) = Some W_a2530.
Proof. vm_refl. Qed.
Lemma D_a2530 : decode_any W_a2530 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2534 : bv 32 := 0x00068593.
Lemma F_a2534 : fetch_word Asan.M.loaded_segments (0xa2584 : word) = Some W_a2534.
Proof. vm_refl. Qed.
Lemma D_a2534 : decode_any W_a2534 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2538 : bv 32 := 0x00000693.
Lemma F_a2538 : fetch_word Asan.M.loaded_segments (0xa2588 : word) = Some W_a2538.
Proof. vm_refl. Qed.
Lemma D_a2538 : decode_any W_a2538 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a253c : bv 32 := 0x0040006f.
Lemma F_a253c : fetch_word Asan.M.loaded_segments (0xa258c : word) = Some W_a253c.
Proof. vm_refl. Qed.
Lemma D_a253c : decode_any W_a253c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2540 : bv 32 := 0xf9010113.
Lemma F_a2540 : fetch_word Asan.M.loaded_segments (0xa2590 : word) = Some W_a2540.
Proof. vm_refl. Qed.
Lemma D_a2540 : decode_any W_a2540 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2544 : bv 32 := 0x06113423.
Lemma F_a2544 : fetch_word Asan.M.loaded_segments (0xa2594 : word) = Some W_a2544.
Proof. vm_refl. Qed.
Lemma D_a2544 : decode_any W_a2544 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2548 : bv 32 := 0x06813023.
Lemma F_a2548 : fetch_word Asan.M.loaded_segments (0xa2598 : word) = Some W_a2548.
Proof. vm_refl. Qed.
Lemma D_a2548 : decode_any W_a2548 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a254c : bv 32 := 0x04913c23.
Lemma F_a254c : fetch_word Asan.M.loaded_segments (0xa259c : word) = Some W_a254c.
Proof. vm_refl. Qed.
Lemma D_a254c : decode_any W_a254c = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2550 : bv 32 := 0x05213823.
Lemma F_a2550 : fetch_word Asan.M.loaded_segments (0xa25a0 : word) = Some W_a2550.
Proof. vm_refl. Qed.
Lemma D_a2550 : decode_any W_a2550 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2554 : bv 32 := 0x05313423.
Lemma F_a2554 : fetch_word Asan.M.loaded_segments (0xa25a4 : word) = Some W_a2554.
Proof. vm_refl. Qed.
Lemma D_a2554 : decode_any W_a2554 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2558 : bv 32 := 0x05413023.
Lemma F_a2558 : fetch_word Asan.M.loaded_segments (0xa25a8 : word) = Some W_a2558.
Proof. vm_refl. Qed.
Lemma D_a2558 : decode_any W_a2558 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a255c : bv 32 := 0x03513c23.
Lemma F_a255c : fetch_word Asan.M.loaded_segments (0xa25ac : word) = Some W_a255c.
Proof. vm_refl. Qed.
Lemma D_a255c : decode_any W_a255c = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2560 : bv 32 := 0x03613823.
Lemma F_a2560 : fetch_word Asan.M.loaded_segments (0xa25b0 : word) = Some W_a2560.
Proof. vm_refl. Qed.
Lemma D_a2560 : decode_any W_a2560 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2564 : bv 32 := 0x03713423.
Lemma F_a2564 : fetch_word Asan.M.loaded_segments (0xa25b4 : word) = Some W_a2564.
Proof. vm_refl. Qed.
Lemma D_a2564 : decode_any W_a2564 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2568 : bv 32 := 0x03813023.
Lemma F_a2568 : fetch_word Asan.M.loaded_segments (0xa25b8 : word) = Some W_a2568.
Proof. vm_refl. Qed.
Lemma D_a2568 : decode_any W_a2568 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a256c : bv 32 := 0x01913c23.
Lemma F_a256c : fetch_word Asan.M.loaded_segments (0xa25bc : word) = Some W_a256c.
Proof. vm_refl. Qed.
Lemma D_a256c : decode_any W_a256c = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2570 : bv 32 := 0x00068413.
Lemma F_a2570 : fetch_word Asan.M.loaded_segments (0xa25c0 : word) = Some W_a2570.
Proof. vm_refl. Qed.
Lemma D_a2570 : decode_any W_a2570 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2574 : bv 32 := 0x00050493.
Lemma F_a2574 : fetch_word Asan.M.loaded_segments (0xa25c4 : word) = Some W_a2574.
Proof. vm_refl. Qed.
Lemma D_a2574 : decode_any W_a2574 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2578 : bv 32 := 0x00b13423.
Lemma F_a2578 : fetch_word Asan.M.loaded_segments (0xa25c8 : word) = Some W_a2578.
Proof. vm_refl. Qed.
Lemma D_a2578 : decode_any W_a2578 = Some (Store SZ8 2 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a257c : bv 32 := 0x00c13823.
Lemma F_a257c : fetch_word Asan.M.loaded_segments (0xa25cc : word) = Some W_a257c.
Proof. vm_refl. Qed.
Lemma D_a257c : decode_any W_a257c = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2580 : bv 32 := 0x00068463.
Lemma F_a2580 : fetch_word Asan.M.loaded_segments (0xa25d0 : word) = Some W_a2580.
Proof. vm_refl. Qed.
Lemma D_a2580 : decode_any W_a2580 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2588 : bv 32 := 0x0006069b.
Lemma F_a2588 : fetch_word Asan.M.loaded_segments (0xa25d8 : word) = Some W_a2588.
Proof. vm_refl. Qed.
Lemma D_a2588 : decode_any W_a2588 = Some (OpImm32 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a258c : bv 32 := 0x00000513.
Lemma F_a258c : fetch_word Asan.M.loaded_segments (0xa25dc : word) = Some W_a258c.
Proof. vm_refl. Qed.
Lemma D_a258c : decode_any W_a258c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2590 : bv 32 := 0x1c068a63.
Lemma F_a2590 : fetch_word Asan.M.loaded_segments (0xa25e0 : word) = Some W_a2590.
Proof. vm_refl. Qed.
Lemma D_a2590 : decode_any W_a2590 = Some (Branch BC_EQ 13 0 468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2594 : bv 32 := 0x1c058863.
Lemma F_a2594 : fetch_word Asan.M.loaded_segments (0xa25e4 : word) = Some W_a2594.
Proof. vm_refl. Qed.
Lemma D_a2594 : decode_any W_a2594 = Some (Branch BC_EQ 11 0 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2598 : bv 32 := 0x02065693.
Lemma F_a2598 : fetch_word Asan.M.loaded_segments (0xa25e8 : word) = Some W_a2598.
Proof. vm_refl. Qed.
Lemma D_a2598 : decode_any W_a2598 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a259c : bv 32 := 0xfff00513.
Lemma F_a259c : fetch_word Asan.M.loaded_segments (0xa25ec : word) = Some W_a259c.
Proof. vm_refl. Qed.
Lemma D_a259c : decode_any W_a259c = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25a0 : bv 32 := 0xfff6e717.
Lemma F_a25a0 : fetch_word Asan.M.loaded_segments (0xa25f0 : word) = Some W_a25a0.
Proof. vm_refl. Qed.
Lemma D_a25a0 : decode_any W_a25a0 = Some (Auipc 14 1048430, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25a4 : bv 32 := 0xfff6e797.
Lemma F_a25a4 : fetch_word Asan.M.loaded_segments (0xa25f4 : word) = Some W_a25a4.
Proof. vm_refl. Qed.
Lemma D_a25a4 : decode_any W_a25a4 = Some (Auipc 15 1048430, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25a8 : bv 32 := 0x02055513.
Lemma F_a25a8 : fetch_word Asan.M.loaded_segments (0xa25f8 : word) = Some W_a25a8.
Proof. vm_refl. Qed.
Lemma D_a25a8 : decode_any W_a25a8 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25ac : bv 32 := 0xd347b783.
Lemma F_a25ac : fetch_word Asan.M.loaded_segments (0xa25fc : word) = Some W_a25ac.
Proof. vm_refl. Qed.
Lemma D_a25ac : decode_any W_a25ac = Some (Load SZ8 true 15 15 3380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25b0 : bv 32 := 0x00a67633.
Lemma F_a25b0 : fetch_word Asan.M.loaded_segments (0xa2600 : word) = Some W_a25b0.
Proof. vm_refl. Qed.
Lemma D_a25b0 : decode_any W_a25b0 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25b4 : bv 32 := 0xfff6e517.
Lemma F_a25b4 : fetch_word Asan.M.loaded_segments (0xa2604 : word) = Some W_a25b4.
Proof. vm_refl. Qed.
Lemma D_a25b4 : decode_any W_a25b4 = Some (Auipc 10 1048430, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25b8 : bv 32 := 0xe3453803.
Lemma F_a25b8 : fetch_word Asan.M.loaded_segments (0xa2608 : word) = Some W_a25b8.
Proof. vm_refl. Qed.
Lemma D_a25b8 : decode_any W_a25b8 = Some (Load SZ8 true 16 10 3636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25bc : bv 32 := 0xcf873503.
Lemma F_a25bc : fetch_word Asan.M.loaded_segments (0xa260c : word) = Some W_a25bc.
Proof. vm_refl. Qed.
Lemma D_a25bc : decode_any W_a25bc = Some (Load SZ8 true 10 14 3320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25c0 : bv 32 := 0x02f60733.
Lemma F_a25c0 : fetch_word Asan.M.loaded_segments (0xa2610 : word) = Some W_a25c0.
Proof. vm_refl. Qed.
Lemma D_a25c0 : decode_any W_a25c0 = Some (Mul M_MUL 14 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25c4 : bv 32 := 0x00361793.
Lemma F_a25c4 : fetch_word Asan.M.loaded_segments (0xa2614 : word) = Some W_a25c4.
Proof. vm_refl. Qed.
Lemma D_a25c4 : decode_any W_a25c4 = Some (ShiftImm ALU_SLL 15 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25c8 : bv 32 := 0x01074633.
Lemma F_a25c8 : fetch_word Asan.M.loaded_segments (0xa2618 : word) = Some W_a25c8.
Proof. vm_refl. Qed.
Lemma D_a25c8 : decode_any W_a25c8 = Some (Op ALU_XOR 12 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25cc : bv 32 := 0x00f58733.
Lemma F_a25cc : fetch_word Asan.M.loaded_segments (0xa261c : word) = Some W_a25cc.
Proof. vm_refl. Qed.
Lemma D_a25cc : decode_any W_a25cc = Some (Op ALU_ADD 14 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25d0 : bv 32 := 0x0005b783.
Lemma F_a25d0 : fetch_word Asan.M.loaded_segments (0xa2620 : word) = Some W_a25d0.
Proof. vm_refl. Qed.
Lemma D_a25d0 : decode_any W_a25d0 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25d4 : bv 32 := 0x00858593.
Lemma F_a25d4 : fetch_word Asan.M.loaded_segments (0xa2624 : word) = Some W_a25d4.
Proof. vm_refl. Qed.
Lemma D_a25d4 : decode_any W_a25d4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25d8 : bv 32 := 0x02a787b3.
Lemma F_a25d8 : fetch_word Asan.M.loaded_segments (0xa2628 : word) = Some W_a25d8.
Proof. vm_refl. Qed.
Lemma D_a25d8 : decode_any W_a25d8 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25dc : bv 32 := 0x02f7d813.
Lemma F_a25dc : fetch_word Asan.M.loaded_segments (0xa262c : word) = Some W_a25dc.
Proof. vm_refl. Qed.
Lemma D_a25dc : decode_any W_a25dc = Some (ShiftImm ALU_SRL 16 15 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25e0 : bv 32 := 0x00f847b3.
Lemma F_a25e0 : fetch_word Asan.M.loaded_segments (0xa2630 : word) = Some W_a25e0.
Proof. vm_refl. Qed.
Lemma D_a25e0 : decode_any W_a25e0 = Some (Op ALU_XOR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25e4 : bv 32 := 0x02a787b3.
Lemma F_a25e4 : fetch_word Asan.M.loaded_segments (0xa2634 : word) = Some W_a25e4.
Proof. vm_refl. Qed.
Lemma D_a25e4 : decode_any W_a25e4 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25e8 : bv 32 := 0x00c7c633.
Lemma F_a25e8 : fetch_word Asan.M.loaded_segments (0xa2638 : word) = Some W_a25e8.
Proof. vm_refl. Qed.
Lemma D_a25e8 : decode_any W_a25e8 = Some (Op ALU_XOR 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25ec : bv 32 := 0x02a60633.
Lemma F_a25ec : fetch_word Asan.M.loaded_segments (0xa263c : word) = Some W_a25ec.
Proof. vm_refl. Qed.
Lemma D_a25ec : decode_any W_a25ec = Some (Mul M_MUL 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25f0 : bv 32 := 0xfee590e3.
Lemma F_a25f0 : fetch_word Asan.M.loaded_segments (0xa2640 : word) = Some W_a25f0.
Proof. vm_refl. Qed.
Lemma D_a25f0 : decode_any W_a25f0 = Some (Branch BC_NE 11 14 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25f4 : bv 32 := 0x00010b37.
Lemma F_a25f4 : fetch_word Asan.M.loaded_segments (0xa2644 : word) = Some W_a25f4.
Proof. vm_refl. Qed.
Lemma D_a25f4 : decode_any W_a25f4 = Some (Lui 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25f8 : bv 32 := 0x80000bb7.
Lemma F_a25f8 : fetch_word Asan.M.loaded_segments (0xa2648 : word) = Some W_a25f8.
Proof. vm_refl. Qed.
Lemma D_a25f8 : decode_any W_a25f8 = Some (Lui 23 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25fc : bv 32 := 0x02a685b3.
Lemma F_a25fc : fetch_word Asan.M.loaded_segments (0xa264c : word) = Some W_a25fc.
Proof. vm_refl. Qed.
Lemma D_a25fc : decode_any W_a25fc = Some (Mul M_MUL 11 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2600 : bv 32 := 0x004006b7.
Lemma F_a2600 : fetch_word Asan.M.loaded_segments (0xa2650 : word) = Some W_a2600.
Proof. vm_refl. Qed.
Lemma D_a2600 : decode_any W_a2600 = Some (Lui 13 1024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2604 : bv 32 := 0xfffb0b1b.
Lemma F_a2604 : fetch_word Asan.M.loaded_segments (0xa2654 : word) = Some W_a2604.
Proof. vm_refl. Qed.
Lemma D_a2604 : decode_any W_a2604 = Some (OpImm32 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2608 : bv 32 := 0xfffb8b9b.
Lemma F_a2608 : fetch_word Asan.M.loaded_segments (0xa2658 : word) = Some W_a2608.
Proof. vm_refl. Qed.
Lemma D_a2608 : decode_any W_a2608 = Some (OpImm32 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a260c : bv 32 := 0x02f5d713.
Lemma F_a260c : fetch_word Asan.M.loaded_segments (0xa265c : word) = Some W_a260c.
Proof. vm_refl. Qed.
Lemma D_a260c : decode_any W_a260c = Some (ShiftImm ALU_SRL 14 11 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2610 : bv 32 := 0x00b745b3.
Lemma F_a2610 : fetch_word Asan.M.loaded_segments (0xa2660 : word) = Some W_a2610.
Proof. vm_refl. Qed.
Lemma D_a2610 : decode_any W_a2610 = Some (Op ALU_XOR 11 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2614 : bv 32 := 0x02a585b3.
Lemma F_a2614 : fetch_word Asan.M.loaded_segments (0xa2664 : word) = Some W_a2614.
Proof. vm_refl. Qed.
Lemma D_a2614 : decode_any W_a2614 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2618 : bv 32 := 0x00c5c5b3.
Lemma F_a2618 : fetch_word Asan.M.loaded_segments (0xa2668 : word) = Some W_a2618.
Proof. vm_refl. Qed.
Lemma D_a2618 : decode_any W_a2618 = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a261c : bv 32 := 0x02a585b3.
Lemma F_a261c : fetch_word Asan.M.loaded_segments (0xa266c : word) = Some W_a261c.
Proof. vm_refl. Qed.
Lemma D_a261c : decode_any W_a261c = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2620 : bv 32 := 0x02f5d613.
Lemma F_a2620 : fetch_word Asan.M.loaded_segments (0xa2670 : word) = Some W_a2620.
Proof. vm_refl. Qed.
Lemma D_a2620 : decode_any W_a2620 = Some (ShiftImm ALU_SRL 12 11 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2624 : bv 32 := 0x00b645b3.
Lemma F_a2624 : fetch_word Asan.M.loaded_segments (0xa2674 : word) = Some W_a2624.
Proof. vm_refl. Qed.
Lemma D_a2624 : decode_any W_a2624 = Some (Op ALU_XOR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2628 : bv 32 := 0x02a58533.
Lemma F_a2628 : fetch_word Asan.M.loaded_segments (0xa2678 : word) = Some W_a2628.
Proof. vm_refl. Qed.
Lemma D_a2628 : decode_any W_a2628 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a262c : bv 32 := 0x02f55593.
Lemma F_a262c : fetch_word Asan.M.loaded_segments (0xa267c : word) = Some W_a262c.
Proof. vm_refl. Qed.
Lemma D_a262c : decode_any W_a262c = Some (ShiftImm ALU_SRL 11 10 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2630 : bv 32 := 0x00a5c9b3.
Lemma F_a2630 : fetch_word Asan.M.loaded_segments (0xa2680 : word) = Some W_a2630.
Proof. vm_refl. Qed.
Lemma D_a2630 : decode_any W_a2630 = Some (Op ALU_XOR 19 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2634 : bv 32 := 0x02c99513.
Lemma F_a2634 : fetch_word Asan.M.loaded_segments (0xa2684 : word) = Some W_a2634.
Proof. vm_refl. Qed.
Lemma D_a2634 : decode_any W_a2634 = Some (ShiftImm ALU_SLL 10 19 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2638 : bv 32 := 0x02a55513.
Lemma F_a2638 : fetch_word Asan.M.loaded_segments (0xa2688 : word) = Some W_a2638.
Proof. vm_refl. Qed.
Lemma D_a2638 : decode_any W_a2638 = Some (ShiftImm ALU_SRL 10 10 42, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a263c : bv 32 := 0x00a48933.
Lemma F_a263c : fetch_word Asan.M.loaded_segments (0xa268c : word) = Some W_a263c.
Proof. vm_refl. Qed.
Lemma D_a263c : decode_any W_a263c = Some (Op ALU_ADD 18 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2640 : bv 32 := 0x00092503.
Lemma F_a2640 : fetch_word Asan.M.loaded_segments (0xa2690 : word) = Some W_a2640.
Proof. vm_refl. Qed.
Lemma D_a2640 : decode_any W_a2640 = Some (Load SZ4 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2644 : bv 32 := 0x01068c1b.
Lemma F_a2644 : fetch_word Asan.M.loaded_segments (0xa2694 : word) = Some W_a2644.
Proof. vm_refl. Qed.
Lemma D_a2644 : decode_any W_a2644 = Some (OpImm32 24 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2648 : bv 32 := 0x01848c33.
Lemma F_a2648 : fetch_word Asan.M.loaded_segments (0xa2698 : word) = Some W_a2648.
Proof. vm_refl. Qed.
Lemma D_a2648 : decode_any W_a2648 = Some (Op ALU_ADD 24 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a264c : bv 32 := 0x0230000f.
Lemma F_a264c : fetch_word Asan.M.loaded_segments (0xa269c : word) = Some W_a264c.
Proof. vm_refl. Qed.
Lemma D_a264c : decode_any W_a264c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2650 : bv 32 := 0x01757cb3.
Lemma F_a2650 : fetch_word Asan.M.loaded_segments (0xa26a0 : word) = Some W_a2650.
Proof. vm_refl. Qed.
Lemma D_a2650 : decode_any W_a2650 = Some (Op ALU_AND 25 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2654 : bv 32 := 0x0086869b.
Lemma F_a2654 : fetch_word Asan.M.loaded_segments (0xa26a4 : word) = Some W_a2654.
Proof. vm_refl. Qed.
Lemma D_a2654 : decode_any W_a2654 = Some (OpImm32 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2658 : bv 32 := 0x00d48a33.
Lemma F_a2658 : fetch_word Asan.M.loaded_segments (0xa26a8 : word) = Some W_a2658.
Proof. vm_refl. Qed.
Lemma D_a2658 : decode_any W_a2658 = Some (Op ALU_ADD 20 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a265c : bv 32 := 0x000c8593.
Lemma F_a265c : fetch_word Asan.M.loaded_segments (0xa26ac : word) = Some W_a265c.
Proof. vm_refl. Qed.
Lemma D_a265c : decode_any W_a265c = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2660 : bv 32 := 0x04058c63.
Lemma F_a2660 : fetch_word Asan.M.loaded_segments (0xa26b0 : word) = Some W_a2660.
Proof. vm_refl. Qed.
Lemma D_a2660 : decode_any W_a2660 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2664 : bv 32 := 0x00058513.
Lemma F_a2664 : fetch_word Asan.M.loaded_segments (0xa26b4 : word) = Some W_a2664.
Proof. vm_refl. Qed.
Lemma D_a2664 : decode_any W_a2664 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2668 : bv 32 := 0x0105d59b.
Lemma F_a2668 : fetch_word Asan.M.loaded_segments (0xa26b8 : word) = Some W_a2668.
Proof. vm_refl. Qed.
Lemma D_a2668 : decode_any W_a2668 = Some (ShiftImm32 ALU_SRL 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a266c : bv 32 := 0x00359613.
Lemma F_a266c : fetch_word Asan.M.loaded_segments (0xa26bc : word) = Some W_a266c.
Proof. vm_refl. Qed.
Lemma D_a266c : decode_any W_a266c = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2670 : bv 32 := 0x00cc0633.
Lemma F_a2670 : fetch_word Asan.M.loaded_segments (0xa26c0 : word) = Some W_a2670.
Proof. vm_refl. Qed.
Lemma D_a2670 : decode_any W_a2670 = Some (Op ALU_ADD 12 24 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2674 : bv 32 := 0x00063603.
Lemma F_a2674 : fetch_word Asan.M.loaded_segments (0xa26c4 : word) = Some W_a2674.
Proof. vm_refl. Qed.
Lemma D_a2674 : decode_any W_a2674 = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2678 : bv 32 := 0x02060463.
Lemma F_a2678 : fetch_word Asan.M.loaded_segments (0xa26c8 : word) = Some W_a2678.
Proof. vm_refl. Qed.
Lemma D_a2678 : decode_any W_a2678 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a267c : bv 32 := 0x02051593.
Lemma F_a267c : fetch_word Asan.M.loaded_segments (0xa26cc : word) = Some W_a267c.
Proof. vm_refl. Qed.
Lemma D_a267c : decode_any W_a267c = Some (ShiftImm ALU_SLL 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2680 : bv 32 := 0x0205d593.
Lemma F_a2680 : fetch_word Asan.M.loaded_segments (0xa26d0 : word) = Some W_a2680.
Proof. vm_refl. Qed.
Lemma D_a2680 : decode_any W_a2680 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2684 : bv 32 := 0x0165f5b3.
Lemma F_a2684 : fetch_word Asan.M.loaded_segments (0xa26d4 : word) = Some W_a2684.
Proof. vm_refl. Qed.
Lemma D_a2684 : decode_any W_a2684 = Some (Op ALU_AND 11 11 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2688 : bv 32 := 0x00459593.
Lemma F_a2688 : fetch_word Asan.M.loaded_segments (0xa26d8 : word) = Some W_a2688.
Proof. vm_refl. Qed.
Lemma D_a2688 : decode_any W_a2688 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a268c : bv 32 := 0x00b605b3.
Lemma F_a268c : fetch_word Asan.M.loaded_segments (0xa26dc : word) = Some W_a268c.
Proof. vm_refl. Qed.
Lemma D_a268c : decode_any W_a268c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2690 : bv 32 := 0x0005b603.
Lemma F_a2690 : fetch_word Asan.M.loaded_segments (0xa26e0 : word) = Some W_a2690.
Proof. vm_refl. Qed.
Lemma D_a2690 : decode_any W_a2690 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2694 : bv 32 := 0x0085a583.
Lemma F_a2694 : fetch_word Asan.M.loaded_segments (0xa26e4 : word) = Some W_a2694.
Proof. vm_refl. Qed.
Lemma D_a2694 : decode_any W_a2694 = Some (Load SZ4 true 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2698 : bv 32 := 0xfcc994e3.
Lemma F_a2698 : fetch_word Asan.M.loaded_segments (0xa26e8 : word) = Some W_a2698.
Proof. vm_refl. Qed.
Lemma D_a2698 : decode_any W_a2698 = Some (Branch BC_NE 19 12 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a269c : bv 32 := 0x0c80006f.
Lemma F_a269c : fetch_word Asan.M.loaded_segments (0xa26ec : word) = Some W_a269c.
Proof. vm_refl. Qed.
Lemma D_a269c : decode_any W_a269c = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26b8 : bv 32 := 0x00090513.
Lemma F_a26b8 : fetch_word Asan.M.loaded_segments (0xa2708 : word) = Some W_a26b8.
Proof. vm_refl. Qed.
Lemma D_a26b8 : decode_any W_a26b8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26bc : bv 32 := 0x5f8000ef.
Lemma F_a26bc : fetch_word Asan.M.loaded_segments (0xa270c : word) = Some W_a26bc.
Proof. vm_refl. Qed.
Lemma D_a26bc : decode_any W_a26bc = Some (Jal 1 1528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26c0 : bv 32 := 0x00050a93.
Lemma F_a26c0 : fetch_word Asan.M.loaded_segments (0xa2710 : word) = Some W_a26c0.
Proof. vm_refl. Qed.
Lemma D_a26c0 : decode_any W_a26c0 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26c4 : bv 32 := 0x03950663.
Lemma F_a26c4 : fetch_word Asan.M.loaded_segments (0xa2714 : word) = Some W_a26c4.
Proof. vm_refl. Qed.
Lemma D_a26c4 : decode_any W_a26c4 = Some (Branch BC_EQ 10 25 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26f0 : bv 32 := 0x00400537.
Lemma F_a26f0 : fetch_word Asan.M.loaded_segments (0xa2740 : word) = Some W_a26f0.
Proof. vm_refl. Qed.
Lemma D_a26f0 : decode_any W_a26f0 = Some (Lui 10 1024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26f4 : bv 32 := 0x00a48533.
Lemma F_a26f4 : fetch_word Asan.M.loaded_segments (0xa2744 : word) = Some W_a26f4.
Proof. vm_refl. Qed.
Lemma D_a26f4 : decode_any W_a26f4 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26f8 : bv 32 := 0x00100593.
Lemma F_a26f8 : fetch_word Asan.M.loaded_segments (0xa2748 : word) = Some W_a26f8.
Proof. vm_refl. Qed.
Lemma D_a26f8 : decode_any W_a26f8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26fc : bv 32 := 0x00b5252f.
Lemma F_a26fc : fetch_word Asan.M.loaded_segments (0xa274c : word) = Some W_a26fc.
Proof. vm_refl. Qed.
Lemma D_a26fc : decode_any W_a26fc = Some (Amo AMO_ADD AW false false 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2700 : bv 32 := 0x0015051b.
Lemma F_a2700 : fetch_word Asan.M.loaded_segments (0xa2750 : word) = Some W_a2700.
Proof. vm_refl. Qed.
Lemma D_a2700 : decode_any W_a2700 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2704 : bv 32 := 0x02051493.
Lemma F_a2704 : fetch_word Asan.M.loaded_segments (0xa2754 : word) = Some W_a2704.
Proof. vm_refl. Qed.
Lemma D_a2704 : decode_any W_a2704 = Some (ShiftImm ALU_SLL 9 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2708 : bv 32 := 0x0204d493.
Lemma F_a2708 : fetch_word Asan.M.loaded_segments (0xa2758 : word) = Some W_a2708.
Proof. vm_refl. Qed.
Lemma D_a2708 : decode_any W_a2708 = Some (ShiftImm ALU_SRL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a270c : bv 32 := 0x08054663.
Lemma F_a270c : fetch_word Asan.M.loaded_segments (0xa275c : word) = Some W_a270c.
Proof. vm_refl. Qed.
Lemma D_a270c : decode_any W_a270c = Some (Branch BC_LT 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2710 : bv 32 := 0x00050b93.
Lemma F_a2710 : fetch_word Asan.M.loaded_segments (0xa2760 : word) = Some W_a2710.
Proof. vm_refl. Qed.
Lemma D_a2710 : decode_any W_a2710 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2714 : bv 32 := 0x0104d593.
Lemma F_a2714 : fetch_word Asan.M.loaded_segments (0xa2764 : word) = Some W_a2714.
Proof. vm_refl. Qed.
Lemma D_a2714 : decode_any W_a2714 = Some (ShiftImm ALU_SRL 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2718 : bv 32 := 0x00359513.
Lemma F_a2718 : fetch_word Asan.M.loaded_segments (0xa2768 : word) = Some W_a2718.
Proof. vm_refl. Qed.
Lemma D_a2718 : decode_any W_a2718 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a271c : bv 32 := 0x00ac0533.
Lemma F_a271c : fetch_word Asan.M.loaded_segments (0xa276c : word) = Some W_a271c.
Proof. vm_refl. Qed.
Lemma D_a271c : decode_any W_a271c = Some (Op ALU_ADD 10 24 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2720 : bv 32 := 0x00053503.
Lemma F_a2720 : fetch_word Asan.M.loaded_segments (0xa2770 : word) = Some W_a2720.
Proof. vm_refl. Qed.
Lemma D_a2720 : decode_any W_a2720 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2724 : bv 32 := 0x08050a63.
Lemma F_a2724 : fetch_word Asan.M.loaded_segments (0xa2774 : word) = Some W_a2724.
Proof. vm_refl. Qed.
Lemma D_a2724 : decode_any W_a2724 = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2728 : bv 32 := 0x0164f5b3.
Lemma F_a2728 : fetch_word Asan.M.loaded_segments (0xa2778 : word) = Some W_a2728.
Proof. vm_refl. Qed.
Lemma D_a2728 : decode_any W_a2728 = Some (Op ALU_AND 11 9 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a272c : bv 32 := 0x00459593.
Lemma F_a272c : fetch_word Asan.M.loaded_segments (0xa277c : word) = Some W_a272c.
Proof. vm_refl. Qed.
Lemma D_a272c : decode_any W_a272c = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2730 : bv 32 := 0x00b504b3.
Lemma F_a2730 : fetch_word Asan.M.loaded_segments (0xa2780 : word) = Some W_a2730.
Proof. vm_refl. Qed.
Lemma D_a2730 : decode_any W_a2730 = Some (Op ALU_ADD 9 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2734 : bv 32 := 0x00810613.
Lemma F_a2734 : fetch_word Asan.M.loaded_segments (0xa2784 : word) = Some W_a2734.
Proof. vm_refl. Qed.
Lemma D_a2734 : decode_any W_a2734 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2738 : bv 32 := 0x00048513.
Lemma F_a2738 : fetch_word Asan.M.loaded_segments (0xa2788 : word) = Some W_a2738.
Proof. vm_refl. Qed.
Lemma D_a2738 : decode_any W_a2738 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a273c : bv 32 := 0x00000593.
Lemma F_a273c : fetch_word Asan.M.loaded_segments (0xa278c : word) = Some W_a273c.
Proof. vm_refl. Qed.
Lemma D_a273c : decode_any W_a273c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2740 : bv 32 := 0x00098693.
Lemma F_a2740 : fetch_word Asan.M.loaded_segments (0xa2790 : word) = Some W_a2740.
Proof. vm_refl. Qed.
Lemma D_a2740 : decode_any W_a2740 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2744 : bv 32 := 0xaf5ff0ef.
Lemma F_a2744 : fetch_word Asan.M.loaded_segments (0xa2794 : word) = Some W_a2744.
Proof. vm_refl. Qed.
Lemma D_a2744 : decode_any W_a2744 = Some (Jal 1 2095860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2748 : bv 32 := 0x0154a423.
Lemma F_a2748 : fetch_word Asan.M.loaded_segments (0xa2798 : word) = Some W_a2748.
Proof. vm_refl. Qed.
Lemma D_a2748 : decode_any W_a2748 = Some (Store SZ4 9 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a274c : bv 32 := 0x0310000f.
Lemma F_a274c : fetch_word Asan.M.loaded_segments (0xa279c : word) = Some W_a274c.
Proof. vm_refl. Qed.
Lemma D_a274c : decode_any W_a274c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2750 : bv 32 := 0x000b8513.
Lemma F_a2750 : fetch_word Asan.M.loaded_segments (0xa27a0 : word) = Some W_a2750.
Proof. vm_refl. Qed.
Lemma D_a2750 : decode_any W_a2750 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2754 : bv 32 := 0x01792023.
Lemma F_a2754 : fetch_word Asan.M.loaded_segments (0xa27a4 : word) = Some W_a2754.
Proof. vm_refl. Qed.
Lemma D_a2754 : decode_any W_a2754 = Some (Store SZ4 18 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2758 : bv 32 := 0x00040663.
Lemma F_a2758 : fetch_word Asan.M.loaded_segments (0xa27a8 : word) = Some W_a2758.
Proof. vm_refl. Qed.
Lemma D_a2758 : decode_any W_a2758 = Some (Branch BC_EQ 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2764 : bv 32 := 0x06813083.
Lemma F_a2764 : fetch_word Asan.M.loaded_segments (0xa27b4 : word) = Some W_a2764.
Proof. vm_refl. Qed.
Lemma D_a2764 : decode_any W_a2764 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2768 : bv 32 := 0x06013403.
Lemma F_a2768 : fetch_word Asan.M.loaded_segments (0xa27b8 : word) = Some W_a2768.
Proof. vm_refl. Qed.
Lemma D_a2768 : decode_any W_a2768 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a276c : bv 32 := 0x05813483.
Lemma F_a276c : fetch_word Asan.M.loaded_segments (0xa27bc : word) = Some W_a276c.
Proof. vm_refl. Qed.
Lemma D_a276c : decode_any W_a276c = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2770 : bv 32 := 0x05013903.
Lemma F_a2770 : fetch_word Asan.M.loaded_segments (0xa27c0 : word) = Some W_a2770.
Proof. vm_refl. Qed.
Lemma D_a2770 : decode_any W_a2770 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2774 : bv 32 := 0x04813983.
Lemma F_a2774 : fetch_word Asan.M.loaded_segments (0xa27c4 : word) = Some W_a2774.
Proof. vm_refl. Qed.
Lemma D_a2774 : decode_any W_a2774 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2778 : bv 32 := 0x04013a03.
Lemma F_a2778 : fetch_word Asan.M.loaded_segments (0xa27c8 : word) = Some W_a2778.
Proof. vm_refl. Qed.
Lemma D_a2778 : decode_any W_a2778 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a277c : bv 32 := 0x03813a83.
Lemma F_a277c : fetch_word Asan.M.loaded_segments (0xa27cc : word) = Some W_a277c.
Proof. vm_refl. Qed.
Lemma D_a277c : decode_any W_a277c = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2780 : bv 32 := 0x03013b03.
Lemma F_a2780 : fetch_word Asan.M.loaded_segments (0xa27d0 : word) = Some W_a2780.
Proof. vm_refl. Qed.
Lemma D_a2780 : decode_any W_a2780 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2784 : bv 32 := 0x02813b83.
Lemma F_a2784 : fetch_word Asan.M.loaded_segments (0xa27d4 : word) = Some W_a2784.
Proof. vm_refl. Qed.
Lemma D_a2784 : decode_any W_a2784 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2788 : bv 32 := 0x02013c03.
Lemma F_a2788 : fetch_word Asan.M.loaded_segments (0xa27d8 : word) = Some W_a2788.
Proof. vm_refl. Qed.
Lemma D_a2788 : decode_any W_a2788 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a278c : bv 32 := 0x01813c83.
Lemma F_a278c : fetch_word Asan.M.loaded_segments (0xa27dc : word) = Some W_a278c.
Proof. vm_refl. Qed.
Lemma D_a278c : decode_any W_a278c = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2790 : bv 32 := 0x07010113.
Lemma F_a2790 : fetch_word Asan.M.loaded_segments (0xa27e0 : word) = Some W_a2790.
Proof. vm_refl. Qed.
Lemma D_a2790 : decode_any W_a2790 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2794 : bv 32 := 0x00008067.
Lemma F_a2794 : fetch_word Asan.M.loaded_segments (0xa27e4 : word) = Some W_a2794.
Proof. vm_refl. Qed.
Lemma D_a2794 : decode_any W_a2794 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cb4 : bv 32 := 0xfd010113.
Lemma F_a2cb4 : fetch_word Asan.M.loaded_segments (0xa2d04 : word) = Some W_a2cb4.
Proof. vm_refl. Qed.
Lemma D_a2cb4 : decode_any W_a2cb4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cb8 : bv 32 := 0x02113423.
Lemma F_a2cb8 : fetch_word Asan.M.loaded_segments (0xa2d08 : word) = Some W_a2cb8.
Proof. vm_refl. Qed.
Lemma D_a2cb8 : decode_any W_a2cb8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cbc : bv 32 := 0x02813023.
Lemma F_a2cbc : fetch_word Asan.M.loaded_segments (0xa2d0c : word) = Some W_a2cbc.
Proof. vm_refl. Qed.
Lemma D_a2cbc : decode_any W_a2cbc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cc0 : bv 32 := 0x00913c23.
Lemma F_a2cc0 : fetch_word Asan.M.loaded_segments (0xa2d10 : word) = Some W_a2cc0.
Proof. vm_refl. Qed.
Lemma D_a2cc0 : decode_any W_a2cc0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cc4 : bv 32 := 0x01213823.
Lemma F_a2cc4 : fetch_word Asan.M.loaded_segments (0xa2d14 : word) = Some W_a2cc4.
Proof. vm_refl. Qed.
Lemma D_a2cc4 : decode_any W_a2cc4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cc8 : bv 32 := 0x01313423.
Lemma F_a2cc8 : fetch_word Asan.M.loaded_segments (0xa2d18 : word) = Some W_a2cc8.
Proof. vm_refl. Qed.
Lemma D_a2cc8 : decode_any W_a2cc8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ccc : bv 32 := 0x00050413.
Lemma F_a2ccc : fetch_word Asan.M.loaded_segments (0xa2d1c : word) = Some W_a2ccc.
Proof. vm_refl. Qed.
Lemma D_a2ccc : decode_any W_a2ccc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cd0 : bv 32 := 0x00000593.
Lemma F_a2cd0 : fetch_word Asan.M.loaded_segments (0xa2d20 : word) = Some W_a2cd0.
Proof. vm_refl. Qed.
Lemma D_a2cd0 : decode_any W_a2cd0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cd4 : bv 32 := 0x800004b7.
Lemma F_a2cd4 : fetch_word Asan.M.loaded_segments (0xa2d24 : word) = Some W_a2cd4.
Proof. vm_refl. Qed.
Lemma D_a2cd4 : decode_any W_a2cd4 = Some (Lui 9 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cd8 : bv 32 := 0x00900913.
Lemma F_a2cd8 : fetch_word Asan.M.loaded_segments (0xa2d28 : word) = Some W_a2cd8.
Proof. vm_refl. Qed.
Lemma D_a2cd8 : decode_any W_a2cd8 = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cdc : bv 32 := 0x00052503.
Lemma F_a2cdc : fetch_word Asan.M.loaded_segments (0xa2d2c : word) = Some W_a2cdc.
Proof. vm_refl. Qed.
Lemma D_a2cdc : decode_any W_a2cdc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ce0 : bv 32 := 0x00055a63.
Lemma F_a2ce0 : fetch_word Asan.M.loaded_segments (0xa2d30 : word) = Some W_a2ce0.
Proof. vm_refl. Qed.
Lemma D_a2ce0 : decode_any W_a2ce0 = Some (Branch BC_GE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cf4 : bv 32 := 0x00956633.
Lemma F_a2cf4 : fetch_word Asan.M.loaded_segments (0xa2d44 : word) = Some W_a2cf4.
Proof. vm_refl. Qed.
Lemma D_a2cf4 : decode_any W_a2cf4 = Some (Op ALU_OR 12 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cf8 : bv 32 := 0x160426af.
Lemma F_a2cf8 : fetch_word Asan.M.loaded_segments (0xa2d48 : word) = Some W_a2cf8.
Proof. vm_refl. Qed.
Lemma D_a2cf8 : decode_any W_a2cf8 = Some (Lr AW true true 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cfc : bv 32 := 0x00a69663.
Lemma F_a2cfc : fetch_word Asan.M.loaded_segments (0xa2d4c : word) = Some W_a2cfc.
Proof. vm_refl. Qed.
Lemma D_a2cfc : decode_any W_a2cfc = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2d00 : bv 32 := 0x1ac4272f.
Lemma F_a2d00 : fetch_word Asan.M.loaded_segments (0xa2d50 : word) = Some W_a2d00.
Proof. vm_refl. Qed.
Lemma D_a2d00 : decode_any W_a2d00 = Some (Sc AW false true 14 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2d04 : bv 32 := 0xfe071ae3.
Lemma F_a2d04 : fetch_word Asan.M.loaded_segments (0xa2d54 : word) = Some W_a2d04.
Proof. vm_refl. Qed.
Lemma D_a2d04 : decode_any W_a2d04 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2d08 : bv 32 := 0x02a68063.
Lemma F_a2d08 : fetch_word Asan.M.loaded_segments (0xa2d58 : word) = Some W_a2d08.
Proof. vm_refl. Qed.
Lemma D_a2d08 : decode_any W_a2d08 = Some (Branch BC_EQ 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2d28 : bv 32 := 0x02813083.
Lemma F_a2d28 : fetch_word Asan.M.loaded_segments (0xa2d78 : word) = Some W_a2d28.
Proof. vm_refl. Qed.
Lemma D_a2d28 : decode_any W_a2d28 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2d2c : bv 32 := 0x02013403.
Lemma F_a2d2c : fetch_word Asan.M.loaded_segments (0xa2d7c : word) = Some W_a2d2c.
Proof. vm_refl. Qed.
Lemma D_a2d2c : decode_any W_a2d2c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2d30 : bv 32 := 0x01813483.
Lemma F_a2d30 : fetch_word Asan.M.loaded_segments (0xa2d80 : word) = Some W_a2d30.
Proof. vm_refl. Qed.
Lemma D_a2d30 : decode_any W_a2d30 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2d34 : bv 32 := 0x01013903.
Lemma F_a2d34 : fetch_word Asan.M.loaded_segments (0xa2d84 : word) = Some W_a2d34.
Proof. vm_refl. Qed.
Lemma D_a2d34 : decode_any W_a2d34 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2d38 : bv 32 := 0x00813983.
Lemma F_a2d38 : fetch_word Asan.M.loaded_segments (0xa2d88 : word) = Some W_a2d38.
Proof. vm_refl. Qed.
Lemma D_a2d38 : decode_any W_a2d38 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2d3c : bv 32 := 0x03010113.
Lemma F_a2d3c : fetch_word Asan.M.loaded_segments (0xa2d8c : word) = Some W_a2d3c.
Proof. vm_refl. Qed.
Lemma D_a2d3c : decode_any W_a2d3c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2d40 : bv 32 := 0x00008067.
Lemma F_a2d40 : fetch_word Asan.M.loaded_segments (0xa2d90 : word) = Some W_a2d40.
Proof. vm_refl. Qed.
Lemma D_a2d40 : decode_any W_a2d40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ea4 : bv 32 := 0x00008513.
Lemma F_a2ea4 : fetch_word Asan.M.loaded_segments (0xa2ef4 : word) = Some W_a2ea4.
Proof. vm_refl. Qed.
Lemma D_a2ea4 : decode_any W_a2ea4 = Some (OpImm ALU_ADD 10 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ea8 : bv 32 := 0x00008067.
Lemma F_a2ea8 : fetch_word Asan.M.loaded_segments (0xa2ef8 : word) = Some W_a2ea8.
Proof. vm_refl. Qed.
Lemma D_a2ea8 : decode_any W_a2ea8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eac : bv 32 := 0xfc010113.
Lemma F_a2eac : fetch_word Asan.M.loaded_segments (0xa2efc : word) = Some W_a2eac.
Proof. vm_refl. Qed.
Lemma D_a2eac : decode_any W_a2eac = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eb0 : bv 32 := 0x02113c23.
Lemma F_a2eb0 : fetch_word Asan.M.loaded_segments (0xa2f00 : word) = Some W_a2eb0.
Proof. vm_refl. Qed.
Lemma D_a2eb0 : decode_any W_a2eb0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eb4 : bv 32 := 0x02813823.
Lemma F_a2eb4 : fetch_word Asan.M.loaded_segments (0xa2f04 : word) = Some W_a2eb4.
Proof. vm_refl. Qed.
Lemma D_a2eb4 : decode_any W_a2eb4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eb8 : bv 32 := 0x02913423.
Lemma F_a2eb8 : fetch_word Asan.M.loaded_segments (0xa2f08 : word) = Some W_a2eb8.
Proof. vm_refl. Qed.
Lemma D_a2eb8 : decode_any W_a2eb8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ebc : bv 32 := 0x03213023.
Lemma F_a2ebc : fetch_word Asan.M.loaded_segments (0xa2f0c : word) = Some W_a2ebc.
Proof. vm_refl. Qed.
Lemma D_a2ebc : decode_any W_a2ebc = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ec0 : bv 32 := 0x01313c23.
Lemma F_a2ec0 : fetch_word Asan.M.loaded_segments (0xa2f10 : word) = Some W_a2ec0.
Proof. vm_refl. Qed.
Lemma D_a2ec0 : decode_any W_a2ec0 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ec4 : bv 32 := 0x01413823.
Lemma F_a2ec4 : fetch_word Asan.M.loaded_segments (0xa2f14 : word) = Some W_a2ec4.
Proof. vm_refl. Qed.
Lemma D_a2ec4 : decode_any W_a2ec4 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ec8 : bv 32 := 0x01513423.
Lemma F_a2ec8 : fetch_word Asan.M.loaded_segments (0xa2f18 : word) = Some W_a2ec8.
Proof. vm_refl. Qed.
Lemma D_a2ec8 : decode_any W_a2ec8 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ecc : bv 32 := 0x01613023.
Lemma F_a2ecc : fetch_word Asan.M.loaded_segments (0xa2f1c : word) = Some W_a2ecc.
Proof. vm_refl. Qed.
Lemma D_a2ecc : decode_any W_a2ecc = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ed0 : bv 32 := 0x00068493.
Lemma F_a2ed0 : fetch_word Asan.M.loaded_segments (0xa2f20 : word) = Some W_a2ed0.
Proof. vm_refl. Qed.
Lemma D_a2ed0 : decode_any W_a2ed0 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ed4 : bv 32 := 0x02079413.
Lemma F_a2ed4 : fetch_word Asan.M.loaded_segments (0xa2f24 : word) = Some W_a2ed4.
Proof. vm_refl. Qed.
Lemma D_a2ed4 : decode_any W_a2ed4 = Some (ShiftImm ALU_SLL 8 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ed8 : bv 32 := 0x00100693.
Lemma F_a2ed8 : fetch_word Asan.M.loaded_segments (0xa2f28 : word) = Some W_a2ed8.
Proof. vm_refl. Qed.
Lemma D_a2ed8 : decode_any W_a2ed8 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2edc : bv 32 := 0x02045413.
Lemma F_a2edc : fetch_word Asan.M.loaded_segments (0xa2f2c : word) = Some W_a2edc.
Proof. vm_refl. Qed.
Lemma D_a2edc : decode_any W_a2edc = Some (ShiftImm ALU_SRL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ee0 : bv 32 := 0x0ef6f863.
Lemma F_a2ee0 : fetch_word Asan.M.loaded_segments (0xa2f30 : word) = Some W_a2ee0.
Proof. vm_refl. Qed.
Lemma D_a2ee0 : decode_any W_a2ee0 = Some (Branch BC_GEU 13 15 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ee4 : bv 32 := 0x000be697.
Lemma F_a2ee4 : fetch_word Asan.M.loaded_segments (0xa2f34 : word) = Some W_a2ee4.
Proof. vm_refl. Qed.
Lemma D_a2ee4 : decode_any W_a2ee4 = Some (Auipc 13 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ee8 : bv 32 := 0xcc46b903.
Lemma F_a2ee8 : fetch_word Asan.M.loaded_segments (0xa2f38 : word) = Some W_a2ee8.
Proof. vm_refl. Qed.
Lemma D_a2ee8 : decode_any W_a2ee8 = Some (Load SZ8 true 18 13 3268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eec : bv 32 := 0x00093683.
Lemma F_a2eec : fetch_word Asan.M.loaded_segments (0xa2f3c : word) = Some W_a2eec.
Proof. vm_refl. Qed.
Lemma D_a2eec : decode_any W_a2eec = Some (Load SZ8 true 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ef0 : bv 32 := 0x00068e63.
Lemma F_a2ef0 : fetch_word Asan.M.loaded_segments (0xa2f40 : word) = Some W_a2ef0.
Proof. vm_refl. Qed.
Lemma D_a2ef0 : decode_any W_a2ef0 = Some (Branch BC_EQ 13 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ef4 : bv 32 := 0x00100793.
Lemma F_a2ef4 : fetch_word Asan.M.loaded_segments (0xa2f44 : word) = Some W_a2ef4.
Proof. vm_refl. Qed.
Lemma D_a2ef4 : decode_any W_a2ef4 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ef8 : bv 32 := 0x00c4d813.
Lemma F_a2ef8 : fetch_word Asan.M.loaded_segments (0xa2f48 : word) = Some W_a2ef8.
Proof. vm_refl. Qed.
Lemma D_a2ef8 : decode_any W_a2ef8 = Some (ShiftImm ALU_SRL 16 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2efc : bv 32 := 0x00f52423.
Lemma F_a2efc : fetch_word Asan.M.loaded_segments (0xa2f4c : word) = Some W_a2efc.
Proof. vm_refl. Qed.
Lemma D_a2efc : decode_any W_a2efc = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f00 : bv 32 := 0x00b53823.
Lemma F_a2f00 : fetch_word Asan.M.loaded_segments (0xa2f50 : word) = Some W_a2f00.
Proof. vm_refl. Qed.
Lemma D_a2f00 : decode_any W_a2f00 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f04 : bv 32 := 0x04081463.
Lemma F_a2f04 : fetch_word Asan.M.loaded_segments (0xa2f54 : word) = Some W_a2f04.
Proof. vm_refl. Qed.
Lemma D_a2f04 : decode_any W_a2f04 = Some (Branch BC_NE 16 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f4c : bv 32 := 0x0a977263.
Lemma F_a2f4c : fetch_word Asan.M.loaded_segments (0xa2f9c : word) = Some W_a2f4c.
Proof. vm_refl. Qed.
Lemma D_a2f4c : decode_any W_a2f4c = Some (Branch BC_GEU 14 9 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f50 : bv 32 := 0x04c77c63.
Lemma F_a2f50 : fetch_word Asan.M.loaded_segments (0xa2fa0 : word) = Some W_a2f50.
Proof. vm_refl. Qed.
Lemma D_a2f50 : decode_any W_a2f50 = Some (Branch BC_GEU 14 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f54 : bv 32 := 0xff048493.
Lemma F_a2f54 : fetch_word Asan.M.loaded_segments (0xa2fa4 : word) = Some W_a2f54.
Proof. vm_refl. Qed.
Lemma D_a2f54 : decode_any W_a2f54 = Some (OpImm ALU_ADD 9 9 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f58 : bv 32 := 0x04967863.
Lemma F_a2f58 : fetch_word Asan.M.loaded_segments (0xa2fa8 : word) = Some W_a2f58.
Proof. vm_refl. Qed.
Lemma D_a2f58 : decode_any W_a2f58 = Some (Branch BC_GEU 12 9 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f5c : bv 32 := 0x00767713.
Lemma F_a2f5c : fetch_word Asan.M.loaded_segments (0xa2fac : word) = Some W_a2f5c.
Proof. vm_refl. Qed.
Lemma D_a2f5c : decode_any W_a2f5c = Some (OpImm ALU_AND 14 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f60 : bv 32 := 0x04071463.
Lemma F_a2f60 : fetch_word Asan.M.loaded_segments (0xa2fb0 : word) = Some W_a2f60.
Proof. vm_refl. Qed.
Lemma D_a2f60 : decode_any W_a2f60 = Some (Branch BC_NE 14 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f64 : bv 32 := 0x01050713.
Lemma F_a2f64 : fetch_word Asan.M.loaded_segments (0xa2fb4 : word) = Some W_a2f64.
Proof. vm_refl. Qed.
Lemma D_a2f64 : decode_any W_a2f64 = Some (OpImm ALU_ADD 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f68 : bv 32 := 0x00100793.
Lemma F_a2f68 : fetch_word Asan.M.loaded_segments (0xa2fb8 : word) = Some W_a2f68.
Proof. vm_refl. Qed.
Lemma D_a2f68 : decode_any W_a2f68 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f6c : bv 32 := 0x0287fe63.
Lemma F_a2f6c : fetch_word Asan.M.loaded_segments (0xa2fbc : word) = Some W_a2f6c.
Proof. vm_refl. Qed.
Lemma D_a2f6c : decode_any W_a2f6c = Some (Branch BC_GEU 15 8 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f70 : bv 32 := 0xff863803.
Lemma F_a2f70 : fetch_word Asan.M.loaded_segments (0xa2fc0 : word) = Some W_a2f70.
Proof. vm_refl. Qed.
Lemma D_a2f70 : decode_any W_a2f70 = Some (Load SZ8 true 16 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f74 : bv 32 := 0x02d86a63.
Lemma F_a2f74 : fetch_word Asan.M.loaded_segments (0xa2fc4 : word) = Some W_a2f74.
Proof. vm_refl. Qed.
Lemma D_a2f74 : decode_any W_a2f74 = Some (Branch BC_LTU 16 13 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f78 : bv 32 := 0x00b80c63.
Lemma F_a2f78 : fetch_word Asan.M.loaded_segments (0xa2fc8 : word) = Some W_a2f78.
Proof. vm_refl. Qed.
Lemma D_a2f78 : decode_any W_a2f78 = Some (Branch BC_EQ 16 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f7c : bv 32 := 0x00379893.
Lemma F_a2f7c : fetch_word Asan.M.loaded_segments (0xa2fcc : word) = Some W_a2f7c.
Proof. vm_refl. Qed.
Lemma D_a2f7c : decode_any W_a2f7c = Some (ShiftImm ALU_SLL 17 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f80 : bv 32 := 0x00178793.
Lemma F_a2f80 : fetch_word Asan.M.loaded_segments (0xa2fd0 : word) = Some W_a2f80.
Proof. vm_refl. Qed.
Lemma D_a2f80 : decode_any W_a2f80 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f84 : bv 32 := 0x011708b3.
Lemma F_a2f84 : fetch_word Asan.M.loaded_segments (0xa2fd4 : word) = Some W_a2f84.
Proof. vm_refl. Qed.
Lemma D_a2f84 : decode_any W_a2f84 = Some (Op ALU_ADD 17 14 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f88 : bv 32 := 0x00f52423.
Lemma F_a2f88 : fetch_word Asan.M.loaded_segments (0xa2fd8 : word) = Some W_a2f88.
Proof. vm_refl. Qed.
Lemma D_a2f88 : decode_any W_a2f88 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f8c : bv 32 := 0x0108b023.
Lemma F_a2f8c : fetch_word Asan.M.loaded_segments (0xa2fdc : word) = Some W_a2f8c.
Proof. vm_refl. Qed.
Lemma D_a2f8c : decode_any W_a2f8c = Some (Store SZ8 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f90 : bv 32 := 0xff063803.
Lemma F_a2f90 : fetch_word Asan.M.loaded_segments (0xa2fe0 : word) = Some W_a2f90.
Proof. vm_refl. Qed.
Lemma D_a2f90 : decode_any W_a2f90 = Some (Load SZ8 true 16 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f94 : bv 32 := 0x01067a63.
Lemma F_a2f94 : fetch_word Asan.M.loaded_segments (0xa2fe4 : word) = Some W_a2f94.
Proof. vm_refl. Qed.
Lemma D_a2f94 : decode_any W_a2f94 = Some (Branch BC_GEU 12 16 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f98 : bv 32 := 0x00987863.
Lemma F_a2f98 : fetch_word Asan.M.loaded_segments (0xa2fe8 : word) = Some W_a2f98.
Proof. vm_refl. Qed.
Lemma D_a2f98 : decode_any W_a2f98 = Some (Branch BC_GEU 16 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f9c : bv 32 := 0x00787893.
Lemma F_a2f9c : fetch_word Asan.M.loaded_segments (0xa2fec : word) = Some W_a2f9c.
Proof. vm_refl. Qed.
Lemma D_a2f9c : decode_any W_a2f9c = Some (OpImm ALU_AND 17 16 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fa0 : bv 32 := 0x00080613.
Lemma F_a2fa0 : fetch_word Asan.M.loaded_segments (0xa2ff0 : word) = Some W_a2fa0.
Proof. vm_refl. Qed.
Lemma D_a2fa0 : decode_any W_a2fa0 = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fa4 : bv 32 := 0xfc0884e3.
Lemma F_a2fa4 : fetch_word Asan.M.loaded_segments (0xa2ff4 : word) = Some W_a2fa4.
Proof. vm_refl. Qed.
Lemma D_a2fa4 : decode_any W_a2fa4 = Some (Branch BC_EQ 17 0 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fa8 : bv 32 := 0x03813083.
Lemma F_a2fa8 : fetch_word Asan.M.loaded_segments (0xa2ff8 : word) = Some W_a2fa8.
Proof. vm_refl. Qed.
Lemma D_a2fa8 : decode_any W_a2fa8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fac : bv 32 := 0x03013403.
Lemma F_a2fac : fetch_word Asan.M.loaded_segments (0xa2ffc : word) = Some W_a2fac.
Proof. vm_refl. Qed.
Lemma D_a2fac : decode_any W_a2fac = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fb0 : bv 32 := 0x02813483.
Lemma F_a2fb0 : fetch_word Asan.M.loaded_segments (0xa3000 : word) = Some W_a2fb0.
Proof. vm_refl. Qed.
Lemma D_a2fb0 : decode_any W_a2fb0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fb4 : bv 32 := 0x02013903.
Lemma F_a2fb4 : fetch_word Asan.M.loaded_segments (0xa3004 : word) = Some W_a2fb4.
Proof. vm_refl. Qed.
Lemma D_a2fb4 : decode_any W_a2fb4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fb8 : bv 32 := 0x01813983.
Lemma F_a2fb8 : fetch_word Asan.M.loaded_segments (0xa3008 : word) = Some W_a2fb8.
Proof. vm_refl. Qed.
Lemma D_a2fb8 : decode_any W_a2fb8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fbc : bv 32 := 0x01013a03.
Lemma F_a2fbc : fetch_word Asan.M.loaded_segments (0xa300c : word) = Some W_a2fbc.
Proof. vm_refl. Qed.
Lemma D_a2fbc : decode_any W_a2fbc = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fc0 : bv 32 := 0x00813a83.
Lemma F_a2fc0 : fetch_word Asan.M.loaded_segments (0xa3010 : word) = Some W_a2fc0.
Proof. vm_refl. Qed.
Lemma D_a2fc0 : decode_any W_a2fc0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fc4 : bv 32 := 0x00013b03.
Lemma F_a2fc4 : fetch_word Asan.M.loaded_segments (0xa3014 : word) = Some W_a2fc4.
Proof. vm_refl. Qed.
Lemma D_a2fc4 : decode_any W_a2fc4 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fc8 : bv 32 := 0x04010113.
Lemma F_a2fc8 : fetch_word Asan.M.loaded_segments (0xa3018 : word) = Some W_a2fc8.
Proof. vm_refl. Qed.
Lemma D_a2fc8 : decode_any W_a2fc8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fcc : bv 32 := 0x00008067.
Lemma F_a2fcc : fetch_word Asan.M.loaded_segments (0xa301c : word) = Some W_a2fcc.
Proof. vm_refl. Qed.
Lemma D_a2fcc : decode_any W_a2fcc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

