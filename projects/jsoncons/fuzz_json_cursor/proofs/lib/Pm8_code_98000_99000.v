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

Definition W_981a4 : bv 32 := 0xf7010113.
Lemma F_981a4 : fetch_word Asan.M.loaded_segments (0x981f4 : word) = Some W_981a4.
Proof. vm_refl. Qed.
Lemma D_981a4 : decode_any W_981a4 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_981a8 : bv 32 := 0x08113423.
Lemma F_981a8 : fetch_word Asan.M.loaded_segments (0x981f8 : word) = Some W_981a8.
Proof. vm_refl. Qed.
Lemma D_981a8 : decode_any W_981a8 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_981ac : bv 32 := 0x08813023.
Lemma F_981ac : fetch_word Asan.M.loaded_segments (0x981fc : word) = Some W_981ac.
Proof. vm_refl. Qed.
Lemma D_981ac : decode_any W_981ac = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_981b0 : bv 32 := 0x06913c23.
Lemma F_981b0 : fetch_word Asan.M.loaded_segments (0x98200 : word) = Some W_981b0.
Proof. vm_refl. Qed.
Lemma D_981b0 : decode_any W_981b0 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_981b4 : bv 32 := 0x07213823.
Lemma F_981b4 : fetch_word Asan.M.loaded_segments (0x98204 : word) = Some W_981b4.
Proof. vm_refl. Qed.
Lemma D_981b4 : decode_any W_981b4 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_981b8 : bv 32 := 0x07313423.
Lemma F_981b8 : fetch_word Asan.M.loaded_segments (0x98208 : word) = Some W_981b8.
Proof. vm_refl. Qed.
Lemma D_981b8 : decode_any W_981b8 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_981bc : bv 32 := 0x07413023.
Lemma F_981bc : fetch_word Asan.M.loaded_segments (0x9820c : word) = Some W_981bc.
Proof. vm_refl. Qed.
Lemma D_981bc : decode_any W_981bc = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_981c0 : bv 32 := 0x05513c23.
Lemma F_981c0 : fetch_word Asan.M.loaded_segments (0x98210 : word) = Some W_981c0.
Proof. vm_refl. Qed.
Lemma D_981c0 : decode_any W_981c0 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_981c4 : bv 32 := 0x05613823.
Lemma F_981c4 : fetch_word Asan.M.loaded_segments (0x98214 : word) = Some W_981c4.
Proof. vm_refl. Qed.
Lemma D_981c4 : decode_any W_981c4 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_981c8 : bv 32 := 0x05713423.
Lemma F_981c8 : fetch_word Asan.M.loaded_segments (0x98218 : word) = Some W_981c8.
Proof. vm_refl. Qed.
Lemma D_981c8 : decode_any W_981c8 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_981cc : bv 32 := 0x05813023.
Lemma F_981cc : fetch_word Asan.M.loaded_segments (0x9821c : word) = Some W_981cc.
Proof. vm_refl. Qed.
Lemma D_981cc : decode_any W_981cc = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_981d0 : bv 32 := 0x03913c23.
Lemma F_981d0 : fetch_word Asan.M.loaded_segments (0x98220 : word) = Some W_981d0.
Proof. vm_refl. Qed.
Lemma D_981d0 : decode_any W_981d0 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_981d4 : bv 32 := 0x03a13823.
Lemma F_981d4 : fetch_word Asan.M.loaded_segments (0x98224 : word) = Some W_981d4.
Proof. vm_refl. Qed.
Lemma D_981d4 : decode_any W_981d4 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_981d8 : bv 32 := 0x03b13423.
Lemma F_981d8 : fetch_word Asan.M.loaded_segments (0x98228 : word) = Some W_981d8.
Proof. vm_refl. Qed.
Lemma D_981d8 : decode_any W_981d8 = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_981dc : bv 32 := 0x00058913.
Lemma F_981dc : fetch_word Asan.M.loaded_segments (0x9822c : word) = Some W_981dc.
Proof. vm_refl. Qed.
Lemma D_981dc : decode_any W_981dc = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_981e0 : bv 32 := 0x000bb597.
Lemma F_981e0 : fetch_word Asan.M.loaded_segments (0x98230 : word) = Some W_981e0.
Proof. vm_refl. Qed.
Lemma D_981e0 : decode_any W_981e0 = Some (Auipc 11 187, 4%Z).
Proof. vm_refl. Qed.

Definition W_981e4 : bv 32 := 0xef85b583.
Lemma F_981e4 : fetch_word Asan.M.loaded_segments (0x98234 : word) = Some W_981e4.
Proof. vm_refl. Qed.
Lemma D_981e4 : decode_any W_981e4 = Some (Load SZ8 true 11 11 3832, 4%Z).
Proof. vm_refl. Qed.

Definition W_981e8 : bv 32 := 0x0895c583.
Lemma F_981e8 : fetch_word Asan.M.loaded_segments (0x98238 : word) = Some W_981e8.
Proof. vm_refl. Qed.
Lemma D_981e8 : decode_any W_981e8 = Some (Load SZ1 false 11 11 137, 4%Z).
Proof. vm_refl. Qed.

Definition W_981ec : bv 32 := 0x18058a63.
Lemma F_981ec : fetch_word Asan.M.loaded_segments (0x9823c : word) = Some W_981ec.
Proof. vm_refl. Qed.
Lemma D_981ec : decode_any W_981ec = Some (Branch BC_EQ 11 0 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_981f0 : bv 32 := 0x00050993.
Lemma F_981f0 : fetch_word Asan.M.loaded_segments (0x98240 : word) = Some W_981f0.
Proof. vm_refl. Qed.
Lemma D_981f0 : decode_any W_981f0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_981f4 : bv 32 := 0x000bb517.
Lemma F_981f4 : fetch_word Asan.M.loaded_segments (0x98244 : word) = Some W_981f4.
Proof. vm_refl. Qed.
Lemma D_981f4 : decode_any W_981f4 = Some (Auipc 10 187, 4%Z).
Proof. vm_refl. Qed.

Definition W_981f8 : bv 32 := 0xf4453d03.
Lemma F_981f8 : fetch_word Asan.M.loaded_segments (0x98248 : word) = Some W_981f8.
Proof. vm_refl. Qed.
Lemma D_981f8 : decode_any W_981f8 = Some (Load SZ8 true 26 10 3908, 4%Z).
Proof. vm_refl. Qed.

Definition W_981fc : bv 32 := 0x0009ba03.
Lemma F_981fc : fetch_word Asan.M.loaded_segments (0x9824c : word) = Some W_981fc.
Proof. vm_refl. Qed.
Lemma D_981fc : decode_any W_981fc = Some (Load SZ8 true 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98200 : bv 32 := 0x000bc517.
Lemma F_98200 : fetch_word Asan.M.loaded_segments (0x98250 : word) = Some W_98200.
Proof. vm_refl. Qed.
Lemma D_98200 : decode_any W_98200 = Some (Auipc 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_98204 : bv 32 := 0x000d2583.
Lemma F_98204 : fetch_word Asan.M.loaded_segments (0x98254 : word) = Some W_98204.
Proof. vm_refl. Qed.
Lemma D_98204 : decode_any W_98204 = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98208 : bv 32 := 0xd0853a83.
Lemma F_98208 : fetch_word Asan.M.loaded_segments (0x98258 : word) = Some W_98208.
Proof. vm_refl. Qed.
Lemma D_98208 : decode_any W_98208 = Some (Load SZ8 true 21 10 3336, 4%Z).
Proof. vm_refl. Qed.

Definition W_9820c : bv 32 := 0x00300513.
Lemma F_9820c : fetch_word Asan.M.loaded_segments (0x9825c : word) = Some W_9820c.
Proof. vm_refl. Qed.
Lemma D_9820c : decode_any W_9820c = Some (OpImm ALU_ADD 10 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_98210 : bv 32 := 0x004a8ab3.
Lemma F_98210 : fetch_word Asan.M.loaded_segments (0x98260 : word) = Some W_98210.
Proof. vm_refl. Qed.
Lemma D_98210 : decode_any W_98210 = Some (Op ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_98214 : bv 32 := 0x1ea5fa63.
Lemma F_98214 : fetch_word Asan.M.loaded_segments (0x98264 : word) = Some W_98214.
Proof. vm_refl. Qed.
Lemma D_98214 : decode_any W_98214 = Some (Branch BC_GEU 11 10 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_98218 : bv 32 := 0x000abb03.
Lemma F_98218 : fetch_word Asan.M.loaded_segments (0x98268 : word) = Some W_98218.
Proof. vm_refl. Qed.
Lemma D_98218 : decode_any W_98218 = Some (Load SZ8 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9821c : bv 32 := 0xfff00513.
Lemma F_9821c : fetch_word Asan.M.loaded_segments (0x9826c : word) = Some W_9821c.
Proof. vm_refl. Qed.
Lemma D_9821c : decode_any W_9821c = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_98220 : bv 32 := 0x0230000f.
Lemma F_98220 : fetch_word Asan.M.loaded_segments (0x98270 : word) = Some W_98220.
Proof. vm_refl. Qed.
Lemma D_98220 : decode_any W_98220 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98224 : bv 32 := 0x14ab0e63.
Lemma F_98224 : fetch_word Asan.M.loaded_segments (0x98274 : word) = Some W_98224.
Proof. vm_refl. Qed.
Lemma D_98224 : decode_any W_98224 = Some (Branch BC_EQ 22 10 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_98228 : bv 32 := 0x080b1263.
Lemma F_98228 : fetch_word Asan.M.loaded_segments (0x98278 : word) = Some W_98228.
Proof. vm_refl. Qed.
Lemma D_98228 : decode_any W_98228 = Some (Branch BC_NE 22 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_982ac : bv 32 := 0x0c0b0a63.
Lemma F_982ac : fetch_word Asan.M.loaded_segments (0x982fc : word) = Some W_982ac.
Proof. vm_refl. Qed.
Lemma D_982ac : decode_any W_982ac = Some (Branch BC_EQ 22 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_982b0 : bv 32 := 0x00c13823.
Lemma F_982b0 : fetch_word Asan.M.loaded_segments (0x98300 : word) = Some W_982b0.
Proof. vm_refl. Qed.
Lemma D_982b0 : decode_any W_982b0 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_982b4 : bv 32 := 0x00d13c23.
Lemma F_982b4 : fetch_word Asan.M.loaded_segments (0x98304 : word) = Some W_982b4.
Proof. vm_refl. Qed.
Lemma D_982b4 : decode_any W_982b4 = Some (Store SZ8 2 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_982b8 : bv 32 := 0x0ff00513.
Lemma F_982b8 : fetch_word Asan.M.loaded_segments (0x98308 : word) = Some W_982b8.
Proof. vm_refl. Qed.
Lemma D_982b8 : decode_any W_982b8 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_982bc : bv 32 := 0x0aaa6863.
Lemma F_982bc : fetch_word Asan.M.loaded_segments (0x9830c : word) = Some W_982bc.
Proof. vm_refl. Qed.
Lemma D_982bc : decode_any W_982bc = Some (Branch BC_LTU 20 10 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_9836c : bv 32 := 0x000b0513.
Lemma F_9836c : fetch_word Asan.M.loaded_segments (0x983bc : word) = Some W_9836c.
Proof. vm_refl. Qed.
Lemma D_9836c : decode_any W_9836c = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98370 : bv 32 := 0x004a1413.
Lemma F_98370 : fetch_word Asan.M.loaded_segments (0x983c0 : word) = Some W_98370.
Proof. vm_refl. Qed.
Lemma D_98370 : decode_any W_98370 = Some (ShiftImm ALU_SLL 8 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_98374 : bv 32 := 0x00850433.
Lemma F_98374 : fetch_word Asan.M.loaded_segments (0x983c4 : word) = Some W_98374.
Proof. vm_refl. Qed.
Lemma D_98374 : decode_any W_98374 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98378 : bv 32 := 0x00843503.
Lemma F_98378 : fetch_word Asan.M.loaded_segments (0x983c8 : word) = Some W_98378.
Proof. vm_refl. Qed.
Lemma D_98378 : decode_any W_98378 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9837c : bv 32 := 0x04050263.
Lemma F_9837c : fetch_word Asan.M.loaded_segments (0x983cc : word) = Some W_9837c.
Proof. vm_refl. Qed.
Lemma D_9837c : decode_any W_9837c = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_98380 : bv 32 := 0x00000513.
Lemma F_98380 : fetch_word Asan.M.loaded_segments (0x983d0 : word) = Some W_98380.
Proof. vm_refl. Qed.
Lemma D_98380 : decode_any W_98380 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98384 : bv 32 := 0x08813083.
Lemma F_98384 : fetch_word Asan.M.loaded_segments (0x983d4 : word) = Some W_98384.
Proof. vm_refl. Qed.
Lemma D_98384 : decode_any W_98384 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_98388 : bv 32 := 0x08013403.
Lemma F_98388 : fetch_word Asan.M.loaded_segments (0x983d8 : word) = Some W_98388.
Proof. vm_refl. Qed.
Lemma D_98388 : decode_any W_98388 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_9838c : bv 32 := 0x07813483.
Lemma F_9838c : fetch_word Asan.M.loaded_segments (0x983dc : word) = Some W_9838c.
Proof. vm_refl. Qed.
Lemma D_9838c : decode_any W_9838c = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_98390 : bv 32 := 0x07013903.
Lemma F_98390 : fetch_word Asan.M.loaded_segments (0x983e0 : word) = Some W_98390.
Proof. vm_refl. Qed.
Lemma D_98390 : decode_any W_98390 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_98394 : bv 32 := 0x06813983.
Lemma F_98394 : fetch_word Asan.M.loaded_segments (0x983e4 : word) = Some W_98394.
Proof. vm_refl. Qed.
Lemma D_98394 : decode_any W_98394 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_98398 : bv 32 := 0x06013a03.
Lemma F_98398 : fetch_word Asan.M.loaded_segments (0x983e8 : word) = Some W_98398.
Proof. vm_refl. Qed.
Lemma D_98398 : decode_any W_98398 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_9839c : bv 32 := 0x05813a83.
Lemma F_9839c : fetch_word Asan.M.loaded_segments (0x983ec : word) = Some W_9839c.
Proof. vm_refl. Qed.
Lemma D_9839c : decode_any W_9839c = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_983a0 : bv 32 := 0x05013b03.
Lemma F_983a0 : fetch_word Asan.M.loaded_segments (0x983f0 : word) = Some W_983a0.
Proof. vm_refl. Qed.
Lemma D_983a0 : decode_any W_983a0 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_983a4 : bv 32 := 0x04813b83.
Lemma F_983a4 : fetch_word Asan.M.loaded_segments (0x983f4 : word) = Some W_983a4.
Proof. vm_refl. Qed.
Lemma D_983a4 : decode_any W_983a4 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_983a8 : bv 32 := 0x04013c03.
Lemma F_983a8 : fetch_word Asan.M.loaded_segments (0x983f8 : word) = Some W_983a8.
Proof. vm_refl. Qed.
Lemma D_983a8 : decode_any W_983a8 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_983ac : bv 32 := 0x03813c83.
Lemma F_983ac : fetch_word Asan.M.loaded_segments (0x983fc : word) = Some W_983ac.
Proof. vm_refl. Qed.
Lemma D_983ac : decode_any W_983ac = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_983b0 : bv 32 := 0x03013d03.
Lemma F_983b0 : fetch_word Asan.M.loaded_segments (0x98400 : word) = Some W_983b0.
Proof. vm_refl. Qed.
Lemma D_983b0 : decode_any W_983b0 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_983b4 : bv 32 := 0x02813d83.
Lemma F_983b4 : fetch_word Asan.M.loaded_segments (0x98404 : word) = Some W_983b4.
Proof. vm_refl. Qed.
Lemma D_983b4 : decode_any W_983b4 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_983b8 : bv 32 := 0x09010113.
Lemma F_983b8 : fetch_word Asan.M.loaded_segments (0x98408 : word) = Some W_983b8.
Proof. vm_refl. Qed.
Lemma D_983b8 : decode_any W_983b8 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_983bc : bv 32 := 0x00008067.
Lemma F_983bc : fetch_word Asan.M.loaded_segments (0x9840c : word) = Some W_983bc.
Proof. vm_refl. Qed.
Lemma D_983bc : decode_any W_983bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

