(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_8207c : bv 32 := 0x000db517.
Lemma F_8207c : fetch_word AsanUbsan.M.loaded_segments (0x820c4 : word) = Some W_8207c.
Proof. vm_refl. Qed.
Lemma D_8207c : decode_any W_8207c = Some (Auipc 10 219, 4%Z).
Proof. vm_refl. Qed.

Definition W_82080 : bv 32 := 0x49850503.
Lemma F_82080 : fetch_word AsanUbsan.M.loaded_segments (0x820c8 : word) = Some W_82080.
Proof. vm_refl. Qed.
Lemma D_82080 : decode_any W_82080 = Some (Load SZ1 true 10 10 1176, 4%Z).
Proof. vm_refl. Qed.

Definition W_82084 : bv 32 := 0x0230000f.
Lemma F_82084 : fetch_word AsanUbsan.M.loaded_segments (0x820cc : word) = Some W_82084.
Proof. vm_refl. Qed.
Lemma D_82084 : decode_any W_82084 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82088 : bv 32 := 0x00a03533.
Lemma F_82088 : fetch_word AsanUbsan.M.loaded_segments (0x820d0 : word) = Some W_82088.
Proof. vm_refl. Qed.
Lemma D_82088 : decode_any W_82088 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8208c : bv 32 := 0x00008067.
Lemma F_8208c : fetch_word AsanUbsan.M.loaded_segments (0x820d4 : word) = Some W_8208c.
Proof. vm_refl. Qed.
Lemma D_8208c : decode_any W_8208c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82090 : bv 32 := 0xfc010113.
Lemma F_82090 : fetch_word AsanUbsan.M.loaded_segments (0x820d8 : word) = Some W_82090.
Proof. vm_refl. Qed.
Lemma D_82090 : decode_any W_82090 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_82094 : bv 32 := 0x02113c23.
Lemma F_82094 : fetch_word AsanUbsan.M.loaded_segments (0x820dc : word) = Some W_82094.
Proof. vm_refl. Qed.
Lemma D_82094 : decode_any W_82094 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82098 : bv 32 := 0x02813823.
Lemma F_82098 : fetch_word AsanUbsan.M.loaded_segments (0x820e0 : word) = Some W_82098.
Proof. vm_refl. Qed.
Lemma D_82098 : decode_any W_82098 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8209c : bv 32 := 0x02913423.
Lemma F_8209c : fetch_word AsanUbsan.M.loaded_segments (0x820e4 : word) = Some W_8209c.
Proof. vm_refl. Qed.
Lemma D_8209c : decode_any W_8209c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_820a0 : bv 32 := 0x03213023.
Lemma F_820a0 : fetch_word AsanUbsan.M.loaded_segments (0x820e8 : word) = Some W_820a0.
Proof. vm_refl. Qed.
Lemma D_820a0 : decode_any W_820a0 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_820a4 : bv 32 := 0x01313c23.
Lemma F_820a4 : fetch_word AsanUbsan.M.loaded_segments (0x820ec : word) = Some W_820a4.
Proof. vm_refl. Qed.
Lemma D_820a4 : decode_any W_820a4 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_820a8 : bv 32 := 0x01413823.
Lemma F_820a8 : fetch_word AsanUbsan.M.loaded_segments (0x820f0 : word) = Some W_820a8.
Proof. vm_refl. Qed.
Lemma D_820a8 : decode_any W_820a8 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_820ac : bv 32 := 0x01513423.
Lemma F_820ac : fetch_word AsanUbsan.M.loaded_segments (0x820f4 : word) = Some W_820ac.
Proof. vm_refl. Qed.
Lemma D_820ac : decode_any W_820ac = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_820b0 : bv 32 := 0x00060a63.
Lemma F_820b0 : fetch_word AsanUbsan.M.loaded_segments (0x820f8 : word) = Some W_820b0.
Proof. vm_refl. Qed.
Lemma D_820b0 : decode_any W_820b0 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_820b4 : bv 32 := 0x000db697.
Lemma F_820b4 : fetch_word AsanUbsan.M.loaded_segments (0x820fc : word) = Some W_820b4.
Proof. vm_refl. Qed.
Lemma D_820b4 : decode_any W_820b4 = Some (Auipc 13 219, 4%Z).
Proof. vm_refl. Qed.

Definition W_820b8 : bv 32 := 0x46068683.
Lemma F_820b8 : fetch_word AsanUbsan.M.loaded_segments (0x82100 : word) = Some W_820b8.
Proof. vm_refl. Qed.
Lemma D_820b8 : decode_any W_820b8 = Some (Load SZ1 true 13 13 1120, 4%Z).
Proof. vm_refl. Qed.

Definition W_820bc : bv 32 := 0x0230000f.
Lemma F_820bc : fetch_word AsanUbsan.M.loaded_segments (0x82104 : word) = Some W_820bc.
Proof. vm_refl. Qed.
Lemma D_820bc : decode_any W_820bc = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_820c0 : bv 32 := 0x0a068a63.
Lemma F_820c0 : fetch_word AsanUbsan.M.loaded_segments (0x82108 : word) = Some W_820c0.
Proof. vm_refl. Qed.
Lemma D_820c0 : decode_any W_820c0 = Some (Branch BC_EQ 13 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_820c4 : bv 32 := 0x00757693.
Lemma F_820c4 : fetch_word AsanUbsan.M.loaded_segments (0x8210c : word) = Some W_820c4.
Proof. vm_refl. Qed.
Lemma D_820c4 : decode_any W_820c4 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_820c8 : bv 32 := 0x42069863.
Lemma F_820c8 : fetch_word AsanUbsan.M.loaded_segments (0x82110 : word) = Some W_820c8.
Proof. vm_refl. Qed.
Lemma D_820c8 : decode_any W_820c8 = Some (Branch BC_NE 13 0 1072, 4%Z).
Proof. vm_refl. Qed.

Definition W_820cc : bv 32 := 0x000d2697.
Lemma F_820cc : fetch_word AsanUbsan.M.loaded_segments (0x82114 : word) = Some W_820cc.
Proof. vm_refl. Qed.
Lemma D_820cc : decode_any W_820cc = Some (Auipc 13 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_820d0 : bv 32 := 0x3ec6b683.
Lemma F_820d0 : fetch_word AsanUbsan.M.loaded_segments (0x82118 : word) = Some W_820d0.
Proof. vm_refl. Qed.
Lemma D_820d0 : decode_any W_820d0 = Some (Load SZ8 true 13 13 1004, 4%Z).
Proof. vm_refl. Qed.

Definition W_820d4 : bv 32 := 0x0006b483.
Lemma F_820d4 : fetch_word AsanUbsan.M.loaded_segments (0x8211c : word) = Some W_820d4.
Proof. vm_refl. Qed.
Lemma D_820d4 : decode_any W_820d4 = Some (Load SZ8 true 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_820d8 : bv 32 := 0xfff48693.
Lemma F_820d8 : fetch_word AsanUbsan.M.loaded_segments (0x82120 : word) = Some W_820d8.
Proof. vm_refl. Qed.
Lemma D_820d8 : decode_any W_820d8 = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_820dc : bv 32 := 0x00d4b733.
Lemma F_820dc : fetch_word AsanUbsan.M.loaded_segments (0x82124 : word) = Some W_820dc.
Proof. vm_refl. Qed.
Lemma D_820dc : decode_any W_820dc = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_820e0 : bv 32 := 0xfff70713.
Lemma F_820e0 : fetch_word AsanUbsan.M.loaded_segments (0x82128 : word) = Some W_820e0.
Proof. vm_refl. Qed.
Lemma D_820e0 : decode_any W_820e0 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_820e4 : bv 32 := 0x00d77733.
Lemma F_820e4 : fetch_word AsanUbsan.M.loaded_segments (0x8212c : word) = Some W_820e4.
Proof. vm_refl. Qed.
Lemma D_820e4 : decode_any W_820e4 = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_820e8 : bv 32 := 0x1ca77c63.
Lemma F_820e8 : fetch_word AsanUbsan.M.loaded_segments (0x82130 : word) = Some W_820e8.
Proof. vm_refl. Qed.
Lemma D_820e8 : decode_any W_820e8 = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_820ec : bv 32 := 0x000d2797.
Lemma F_820ec : fetch_word AsanUbsan.M.loaded_segments (0x82134 : word) = Some W_820ec.
Proof. vm_refl. Qed.
Lemma D_820ec : decode_any W_820ec = Some (Auipc 15 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_820f0 : bv 32 := 0x3d47b783.
Lemma F_820f0 : fetch_word AsanUbsan.M.loaded_segments (0x82138 : word) = Some W_820f0.
Proof. vm_refl. Qed.
Lemma D_820f0 : decode_any W_820f0 = Some (Load SZ8 true 15 15 980, 4%Z).
Proof. vm_refl. Qed.

Definition W_820f4 : bv 32 := 0x000d2817.
Lemma F_820f4 : fetch_word AsanUbsan.M.loaded_segments (0x8213c : word) = Some W_820f4.
Proof. vm_refl. Qed.
Lemma D_820f4 : decode_any W_820f4 = Some (Auipc 16 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_820f8 : bv 32 := 0x3d483803.
Lemma F_820f8 : fetch_word AsanUbsan.M.loaded_segments (0x82140 : word) = Some W_820f8.
Proof. vm_refl. Qed.
Lemma D_820f8 : decode_any W_820f8 = Some (Load SZ8 true 16 16 980, 4%Z).
Proof. vm_refl. Qed.

Definition W_820fc : bv 32 := 0x0007b883.
Lemma F_820fc : fetch_word AsanUbsan.M.loaded_segments (0x82144 : word) = Some W_820fc.
Proof. vm_refl. Qed.
Lemma D_820fc : decode_any W_820fc = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82100 : bv 32 := 0x00083783.
Lemma F_82100 : fetch_word AsanUbsan.M.loaded_segments (0x82148 : word) = Some W_82100.
Proof. vm_refl. Qed.
Lemma D_82100 : decode_any W_82100 = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82104 : bv 32 := 0xfff88813.
Lemma F_82104 : fetch_word AsanUbsan.M.loaded_segments (0x8214c : word) = Some W_82104.
Proof. vm_refl. Qed.
Lemma D_82104 : decode_any W_82104 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82108 : bv 32 := 0x00a87463.
Lemma F_82108 : fetch_word AsanUbsan.M.loaded_segments (0x82150 : word) = Some W_82108.
Proof. vm_refl. Qed.
Lemma D_82108 : decode_any W_82108 = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82110 : bv 32 := 0x000d2297.
Lemma F_82110 : fetch_word AsanUbsan.M.loaded_segments (0x82158 : word) = Some W_82110.
Proof. vm_refl. Qed.
Lemma D_82110 : decode_any W_82110 = Some (Auipc 5 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_82114 : bv 32 := 0x3c02b283.
Lemma F_82114 : fetch_word AsanUbsan.M.loaded_segments (0x8215c : word) = Some W_82114.
Proof. vm_refl. Qed.
Lemma D_82114 : decode_any W_82114 = Some (Load SZ8 true 5 5 960, 4%Z).
Proof. vm_refl. Qed.

Definition W_82118 : bv 32 := 0x0002be03.
Lemma F_82118 : fetch_word AsanUbsan.M.loaded_segments (0x82160 : word) = Some W_82118.
Proof. vm_refl. Qed.
Lemma D_82118 : decode_any W_82118 = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8211c : bv 32 := 0x003e5313.
Lemma F_8211c : fetch_word AsanUbsan.M.loaded_segments (0x82164 : word) = Some W_8211c.
Proof. vm_refl. Qed.
Lemma D_8211c : decode_any W_8211c = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82120 : bv 32 := 0x009303b3.
Lemma F_82120 : fetch_word AsanUbsan.M.loaded_segments (0x82168 : word) = Some W_82120.
Proof. vm_refl. Qed.
Lemma D_82120 : decode_any W_82120 = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_82124 : bv 32 := 0x00ae6463.
Lemma F_82124 : fetch_word AsanUbsan.M.loaded_segments (0x8216c : word) = Some W_82124.
Proof. vm_refl. Qed.
Lemma D_82124 : decode_any W_82124 = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82128 : bv 32 := 0x0ca3e463.
Lemma F_82128 : fetch_word AsanUbsan.M.loaded_segments (0x82170 : word) = Some W_82128.
Proof. vm_refl. Qed.
Lemma D_82128 : decode_any W_82128 = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_821f0 : bv 32 := 0x0002b383.
Lemma F_821f0 : fetch_word AsanUbsan.M.loaded_segments (0x82238 : word) = Some W_821f0.
Proof. vm_refl. Qed.
Lemma D_821f0 : decode_any W_821f0 = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_821f4 : bv 32 := 0x0033d293.
Lemma F_821f4 : fetch_word AsanUbsan.M.loaded_segments (0x8223c : word) = Some W_821f4.
Proof. vm_refl. Qed.
Lemma D_821f4 : decode_any W_821f4 = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_821f8 : bv 32 := 0x00928333.
Lemma F_821f8 : fetch_word AsanUbsan.M.loaded_segments (0x82240 : word) = Some W_821f8.
Proof. vm_refl. Qed.
Lemma D_821f8 : decode_any W_821f8 = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_821fc : bv 32 := 0x00a3e463.
Lemma F_821fc : fetch_word AsanUbsan.M.loaded_segments (0x82244 : word) = Some W_821fc.
Proof. vm_refl. Qed.
Lemma D_821fc : decode_any W_821fc = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82200 : bv 32 := 0x0ca36063.
Lemma F_82200 : fetch_word AsanUbsan.M.loaded_segments (0x82248 : word) = Some W_82200.
Proof. vm_refl. Qed.
Lemma D_82200 : decode_any W_82200 = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_822c0 : bv 32 := 0x0075f793.
Lemma F_822c0 : fetch_word AsanUbsan.M.loaded_segments (0x82308 : word) = Some W_822c0.
Proof. vm_refl. Qed.
Lemma D_822c0 : decode_any W_822c0 = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_822c4 : bv 32 := 0x26079a63.
Lemma F_822c4 : fetch_word AsanUbsan.M.loaded_segments (0x8230c : word) = Some W_822c4.
Proof. vm_refl. Qed.
Lemma D_822c4 : decode_any W_822c4 = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

Definition W_822c8 : bv 32 := 0x00b505b3.
Lemma F_822c8 : fetch_word AsanUbsan.M.loaded_segments (0x82310 : word) = Some W_822c8.
Proof. vm_refl. Qed.
Lemma D_822c8 : decode_any W_822c8 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_822cc : bv 32 := 0xff858593.
Lemma F_822cc : fetch_word AsanUbsan.M.loaded_segments (0x82314 : word) = Some W_822cc.
Proof. vm_refl. Qed.
Lemma D_822cc : decode_any W_822cc = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_822d0 : bv 32 := 0x04b77263.
Lemma F_822d0 : fetch_word AsanUbsan.M.loaded_segments (0x82318 : word) = Some W_822d0.
Proof. vm_refl. Qed.
Lemma D_822d0 : decode_any W_822d0 = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_822d4 : bv 32 := 0x000d2717.
Lemma F_822d4 : fetch_word AsanUbsan.M.loaded_segments (0x8231c : word) = Some W_822d4.
Proof. vm_refl. Qed.
Lemma D_822d4 : decode_any W_822d4 = Some (Auipc 14 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_822d8 : bv 32 := 0x1ec73703.
Lemma F_822d8 : fetch_word AsanUbsan.M.loaded_segments (0x82320 : word) = Some W_822d8.
Proof. vm_refl. Qed.
Lemma D_822d8 : decode_any W_822d8 = Some (Load SZ8 true 14 14 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_822dc : bv 32 := 0x000d2797.
Lemma F_822dc : fetch_word AsanUbsan.M.loaded_segments (0x82324 : word) = Some W_822dc.
Proof. vm_refl. Qed.
Lemma D_822dc : decode_any W_822dc = Some (Auipc 15 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_822e0 : bv 32 := 0x1ec7b783.
Lemma F_822e0 : fetch_word AsanUbsan.M.loaded_segments (0x82328 : word) = Some W_822e0.
Proof. vm_refl. Qed.
Lemma D_822e0 : decode_any W_822e0 = Some (Load SZ8 true 15 15 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_822e4 : bv 32 := 0x00073883.
Lemma F_822e4 : fetch_word AsanUbsan.M.loaded_segments (0x8232c : word) = Some W_822e4.
Proof. vm_refl. Qed.
Lemma D_822e4 : decode_any W_822e4 = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_822e8 : bv 32 := 0x0007b703.
Lemma F_822e8 : fetch_word AsanUbsan.M.loaded_segments (0x82330 : word) = Some W_822e8.
Proof. vm_refl. Qed.
Lemma D_822e8 : decode_any W_822e8 = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_822ec : bv 32 := 0xfff88813.
Lemma F_822ec : fetch_word AsanUbsan.M.loaded_segments (0x82334 : word) = Some W_822ec.
Proof. vm_refl. Qed.
Lemma D_822ec : decode_any W_822ec = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_822f0 : bv 32 := 0x00b87463.
Lemma F_822f0 : fetch_word AsanUbsan.M.loaded_segments (0x82338 : word) = Some W_822f0.
Proof. vm_refl. Qed.
Lemma D_822f0 : decode_any W_822f0 = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_822f8 : bv 32 := 0x000d2797.
Lemma F_822f8 : fetch_word AsanUbsan.M.loaded_segments (0x82340 : word) = Some W_822f8.
Proof. vm_refl. Qed.
Lemma D_822f8 : decode_any W_822f8 = Some (Auipc 15 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_822fc : bv 32 := 0x1d87b783.
Lemma F_822fc : fetch_word AsanUbsan.M.loaded_segments (0x82344 : word) = Some W_822fc.
Proof. vm_refl. Qed.
Lemma D_822fc : decode_any W_822fc = Some (Load SZ8 true 15 15 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_82300 : bv 32 := 0x0007b303.
Lemma F_82300 : fetch_word AsanUbsan.M.loaded_segments (0x82348 : word) = Some W_82300.
Proof. vm_refl. Qed.
Lemma D_82300 : decode_any W_82300 = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82304 : bv 32 := 0x00335793.
Lemma F_82304 : fetch_word AsanUbsan.M.loaded_segments (0x8234c : word) = Some W_82304.
Proof. vm_refl. Qed.
Lemma D_82304 : decode_any W_82304 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82308 : bv 32 := 0x009782b3.
Lemma F_82308 : fetch_word AsanUbsan.M.loaded_segments (0x82350 : word) = Some W_82308.
Proof. vm_refl. Qed.
Lemma D_82308 : decode_any W_82308 = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_8230c : bv 32 := 0x12b36263.
Lemma F_8230c : fetch_word AsanUbsan.M.loaded_segments (0x82354 : word) = Some W_8230c.
Proof. vm_refl. Qed.
Lemma D_8230c : decode_any W_8230c = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_82310 : bv 32 := 0x12b2f063.
Lemma F_82310 : fetch_word AsanUbsan.M.loaded_segments (0x82358 : word) = Some W_82310.
Proof. vm_refl. Qed.
Lemma D_82310 : decode_any W_82310 = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_82314 : bv 32 := 0x000d2697.
Lemma F_82314 : fetch_word AsanUbsan.M.loaded_segments (0x8235c : word) = Some W_82314.
Proof. vm_refl. Qed.
Lemma D_82314 : decode_any W_82314 = Some (Auipc 13 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_82318 : bv 32 := 0x1c46b983.
Lemma F_82318 : fetch_word AsanUbsan.M.loaded_segments (0x82360 : word) = Some W_82318.
Proof. vm_refl. Qed.
Lemma D_82318 : decode_any W_82318 = Some (Load SZ8 true 19 13 452, 4%Z).
Proof. vm_refl. Qed.

Definition W_8231c : bv 32 := 0x0009b303.
Lemma F_8231c : fetch_word AsanUbsan.M.loaded_segments (0x82364 : word) = Some W_8231c.
Proof. vm_refl. Qed.
Lemma D_8231c : decode_any W_8231c = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82320 : bv 32 := 0x22030c63.
Lemma F_82320 : fetch_word AsanUbsan.M.loaded_segments (0x82368 : word) = Some W_82320.
Proof. vm_refl. Qed.
Lemma D_82320 : decode_any W_82320 = Some (Branch BC_EQ 6 0 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_82324 : bv 32 := 0x00355693.
Lemma F_82324 : fetch_word AsanUbsan.M.loaded_segments (0x8236c : word) = Some W_82324.
Proof. vm_refl. Qed.
Lemma D_82324 : decode_any W_82324 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82328 : bv 32 := 0x0035d593.
Lemma F_82328 : fetch_word AsanUbsan.M.loaded_segments (0x82370 : word) = Some W_82328.
Proof. vm_refl. Qed.
Lemma D_82328 : decode_any W_82328 = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8232c : bv 32 := 0x00d48533.
Lemma F_8232c : fetch_word AsanUbsan.M.loaded_segments (0x82374 : word) = Some W_8232c.
Proof. vm_refl. Qed.
Lemma D_8232c : decode_any W_8232c = Some (Op ALU_ADD 10 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_82330 : bv 32 := 0x00158913.
Lemma F_82330 : fetch_word AsanUbsan.M.loaded_segments (0x82378 : word) = Some W_82330.
Proof. vm_refl. Qed.
Lemma D_82330 : decode_any W_82330 = Some (OpImm ALU_ADD 18 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82334 : bv 32 := 0x40d90433.
Lemma F_82334 : fetch_word AsanUbsan.M.loaded_segments (0x8237c : word) = Some W_82334.
Proof. vm_refl. Qed.
Lemma D_82334 : decode_any W_82334 = Some (Op ALU_SUB 8 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_82338 : bv 32 := 0x0c061063.
Lemma F_82338 : fetch_word AsanUbsan.M.loaded_segments (0x82380 : word) = Some W_82338.
Proof. vm_refl. Qed.
Lemma D_82338 : decode_any W_82338 = Some (Branch BC_NE 12 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_8233c : bv 32 := 0x000d2597.
Lemma F_8233c : fetch_word AsanUbsan.M.loaded_segments (0x82384 : word) = Some W_8233c.
Proof. vm_refl. Qed.
Lemma D_8233c : decode_any W_8233c = Some (Auipc 11 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_82340 : bv 32 := 0x16c5b583.
Lemma F_82340 : fetch_word AsanUbsan.M.loaded_segments (0x82388 : word) = Some W_82340.
Proof. vm_refl. Qed.
Lemma D_82340 : decode_any W_82340 = Some (Load SZ8 true 11 11 364, 4%Z).
Proof. vm_refl. Qed.

Definition W_82344 : bv 32 := 0x0785b583.
Lemma F_82344 : fetch_word AsanUbsan.M.loaded_segments (0x8238c : word) = Some W_82344.
Proof. vm_refl. Qed.
Lemma D_82344 : decode_any W_82344 = Some (Load SZ8 true 11 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_82348 : bv 32 := 0x0ab46863.
Lemma F_82348 : fetch_word AsanUbsan.M.loaded_segments (0x82390 : word) = Some W_82348.
Proof. vm_refl. Qed.
Lemma D_82348 : decode_any W_82348 = Some (Branch BC_LTU 8 11 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_823f8 : bv 32 := 0x00060593.
Lemma F_823f8 : fetch_word AsanUbsan.M.loaded_segments (0x82440 : word) = Some W_823f8.
Proof. vm_refl. Qed.
Lemma D_823f8 : decode_any W_823f8 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_823fc : bv 32 := 0x00c0006f.
Lemma F_823fc : fetch_word AsanUbsan.M.loaded_segments (0x82444 : word) = Some W_823fc.
Proof. vm_refl. Qed.
Lemma D_823fc : decode_any W_823fc = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82408 : bv 32 := 0x00040613.
Lemma F_82408 : fetch_word AsanUbsan.M.loaded_segments (0x82450 : word) = Some W_82408.
Proof. vm_refl. Qed.
Lemma D_82408 : decode_any W_82408 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8240c : bv 32 := 0x03813083.
Lemma F_8240c : fetch_word AsanUbsan.M.loaded_segments (0x82454 : word) = Some W_8240c.
Proof. vm_refl. Qed.
Lemma D_8240c : decode_any W_8240c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82410 : bv 32 := 0x03013403.
Lemma F_82410 : fetch_word AsanUbsan.M.loaded_segments (0x82458 : word) = Some W_82410.
Proof. vm_refl. Qed.
Lemma D_82410 : decode_any W_82410 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_82414 : bv 32 := 0x02813483.
Lemma F_82414 : fetch_word AsanUbsan.M.loaded_segments (0x8245c : word) = Some W_82414.
Proof. vm_refl. Qed.
Lemma D_82414 : decode_any W_82414 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82418 : bv 32 := 0x02013903.
Lemma F_82418 : fetch_word AsanUbsan.M.loaded_segments (0x82460 : word) = Some W_82418.
Proof. vm_refl. Qed.
Lemma D_82418 : decode_any W_82418 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8241c : bv 32 := 0x01813983.
Lemma F_8241c : fetch_word AsanUbsan.M.loaded_segments (0x82464 : word) = Some W_8241c.
Proof. vm_refl. Qed.
Lemma D_8241c : decode_any W_8241c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82420 : bv 32 := 0x01013a03.
Lemma F_82420 : fetch_word AsanUbsan.M.loaded_segments (0x82468 : word) = Some W_82420.
Proof. vm_refl. Qed.
Lemma D_82420 : decode_any W_82420 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82424 : bv 32 := 0x00813a83.
Lemma F_82424 : fetch_word AsanUbsan.M.loaded_segments (0x8246c : word) = Some W_82424.
Proof. vm_refl. Qed.
Lemma D_82424 : decode_any W_82424 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82428 : bv 32 := 0x04010113.
Lemma F_82428 : fetch_word AsanUbsan.M.loaded_segments (0x82470 : word) = Some W_82428.
Proof. vm_refl. Qed.
Lemma D_82428 : decode_any W_82428 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8242c : bv 32 := 0x00030067.
Lemma F_8242c : fetch_word AsanUbsan.M.loaded_segments (0x82474 : word) = Some W_8242c.
Proof. vm_refl. Qed.
Lemma D_8242c : decode_any W_8242c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8258c : bv 32 := 0x000d2597.
Lemma F_8258c : fetch_word AsanUbsan.M.loaded_segments (0x825d4 : word) = Some W_8258c.
Proof. vm_refl. Qed.
Lemma D_8258c : decode_any W_8258c = Some (Auipc 11 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_82590 : bv 32 := 0xf2c5b583.
Lemma F_82590 : fetch_word AsanUbsan.M.loaded_segments (0x825d8 : word) = Some W_82590.
Proof. vm_refl. Qed.
Lemma D_82590 : decode_any W_82590 = Some (Load SZ8 true 11 11 3884, 4%Z).
Proof. vm_refl. Qed.

Definition W_82594 : bv 32 := 0x0005b583.
Lemma F_82594 : fetch_word AsanUbsan.M.loaded_segments (0x825dc : word) = Some W_82594.
Proof. vm_refl. Qed.
Lemma D_82594 : decode_any W_82594 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82598 : bv 32 := 0xfff58613.
Lemma F_82598 : fetch_word AsanUbsan.M.loaded_segments (0x825e0 : word) = Some W_82598.
Proof. vm_refl. Qed.
Lemma D_82598 : decode_any W_82598 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8259c : bv 32 := 0x00c5b6b3.
Lemma F_8259c : fetch_word AsanUbsan.M.loaded_segments (0x825e4 : word) = Some W_8259c.
Proof. vm_refl. Qed.
Lemma D_8259c : decode_any W_8259c = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_825a0 : bv 32 := 0xfff68693.
Lemma F_825a0 : fetch_word AsanUbsan.M.loaded_segments (0x825e8 : word) = Some W_825a0.
Proof. vm_refl. Qed.
Lemma D_825a0 : decode_any W_825a0 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_825a4 : bv 32 := 0x00c6f6b3.
Lemma F_825a4 : fetch_word AsanUbsan.M.loaded_segments (0x825ec : word) = Some W_825a4.
Proof. vm_refl. Qed.
Lemma D_825a4 : decode_any W_825a4 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_825a8 : bv 32 := 0x04a6f263.
Lemma F_825a8 : fetch_word AsanUbsan.M.loaded_segments (0x825f0 : word) = Some W_825a8.
Proof. vm_refl. Qed.
Lemma D_825a8 : decode_any W_825a8 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_825ac : bv 32 := 0x000d2697.
Lemma F_825ac : fetch_word AsanUbsan.M.loaded_segments (0x825f4 : word) = Some W_825ac.
Proof. vm_refl. Qed.
Lemma D_825ac : decode_any W_825ac = Some (Auipc 13 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_825b0 : bv 32 := 0xf146b683.
Lemma F_825b0 : fetch_word AsanUbsan.M.loaded_segments (0x825f8 : word) = Some W_825b0.
Proof. vm_refl. Qed.
Lemma D_825b0 : decode_any W_825b0 = Some (Load SZ8 true 13 13 3860, 4%Z).
Proof. vm_refl. Qed.

Definition W_825b4 : bv 32 := 0x000d2717.
Lemma F_825b4 : fetch_word AsanUbsan.M.loaded_segments (0x825fc : word) = Some W_825b4.
Proof. vm_refl. Qed.
Lemma D_825b4 : decode_any W_825b4 = Some (Auipc 14 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_825b8 : bv 32 := 0xf1473703.
Lemma F_825b8 : fetch_word AsanUbsan.M.loaded_segments (0x82600 : word) = Some W_825b8.
Proof. vm_refl. Qed.
Lemma D_825b8 : decode_any W_825b8 = Some (Load SZ8 true 14 14 3860, 4%Z).
Proof. vm_refl. Qed.

Definition W_825bc : bv 32 := 0x0006b803.
Lemma F_825bc : fetch_word AsanUbsan.M.loaded_segments (0x82604 : word) = Some W_825bc.
Proof. vm_refl. Qed.
Lemma D_825bc : decode_any W_825bc = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_825c0 : bv 32 := 0x00073683.
Lemma F_825c0 : fetch_word AsanUbsan.M.loaded_segments (0x82608 : word) = Some W_825c0.
Proof. vm_refl. Qed.
Lemma D_825c0 : decode_any W_825c0 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_825c4 : bv 32 := 0xfff80793.
Lemma F_825c4 : fetch_word AsanUbsan.M.loaded_segments (0x8260c : word) = Some W_825c4.
Proof. vm_refl. Qed.
Lemma D_825c4 : decode_any W_825c4 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_825c8 : bv 32 := 0x00a7f463.
Lemma F_825c8 : fetch_word AsanUbsan.M.loaded_segments (0x82610 : word) = Some W_825c8.
Proof. vm_refl. Qed.
Lemma D_825c8 : decode_any W_825c8 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_825d0 : bv 32 := 0x000d2717.
Lemma F_825d0 : fetch_word AsanUbsan.M.loaded_segments (0x82618 : word) = Some W_825d0.
Proof. vm_refl. Qed.
Lemma D_825d0 : decode_any W_825d0 = Some (Auipc 14 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_825d4 : bv 32 := 0xf0073703.
Lemma F_825d4 : fetch_word AsanUbsan.M.loaded_segments (0x8261c : word) = Some W_825d4.
Proof. vm_refl. Qed.
Lemma D_825d4 : decode_any W_825d4 = Some (Load SZ8 true 14 14 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_825d8 : bv 32 := 0x00073283.
Lemma F_825d8 : fetch_word AsanUbsan.M.loaded_segments (0x82620 : word) = Some W_825d8.
Proof. vm_refl. Qed.
Lemma D_825d8 : decode_any W_825d8 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_825dc : bv 32 := 0x0032d713.
Lemma F_825dc : fetch_word AsanUbsan.M.loaded_segments (0x82624 : word) = Some W_825dc.
Proof. vm_refl. Qed.
Lemma D_825dc : decode_any W_825dc = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_825e0 : bv 32 := 0x00b708b3.
Lemma F_825e0 : fetch_word AsanUbsan.M.loaded_segments (0x82628 : word) = Some W_825e0.
Proof. vm_refl. Qed.
Lemma D_825e0 : decode_any W_825e0 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_825e4 : bv 32 := 0x00a2ea63.
Lemma F_825e4 : fetch_word AsanUbsan.M.loaded_segments (0x8262c : word) = Some W_825e4.
Proof. vm_refl. Qed.
Lemma D_825e4 : decode_any W_825e4 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_825e8 : bv 32 := 0x00a8f863.
Lemma F_825e8 : fetch_word AsanUbsan.M.loaded_segments (0x82630 : word) = Some W_825e8.
Proof. vm_refl. Qed.
Lemma D_825e8 : decode_any W_825e8 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_825ec : bv 32 := 0x00355513.
Lemma F_825ec : fetch_word AsanUbsan.M.loaded_segments (0x82634 : word) = Some W_825ec.
Proof. vm_refl. Qed.
Lemma D_825ec : decode_any W_825ec = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_825f0 : bv 32 := 0x00a58533.
Lemma F_825f0 : fetch_word AsanUbsan.M.loaded_segments (0x82638 : word) = Some W_825f0.
Proof. vm_refl. Qed.
Lemma D_825f0 : decode_any W_825f0 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_825f4 : bv 32 := 0x00008067.
Lemma F_825f4 : fetch_word AsanUbsan.M.loaded_segments (0x8263c : word) = Some W_825f4.
Proof. vm_refl. Qed.
Lemma D_825f4 : decode_any W_825f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a18 : bv 32 := 0xfc010113.
Lemma F_82a18 : fetch_word AsanUbsan.M.loaded_segments (0x82a60 : word) = Some W_82a18.
Proof. vm_refl. Qed.
Lemma D_82a18 : decode_any W_82a18 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a1c : bv 32 := 0x02113c23.
Lemma F_82a1c : fetch_word AsanUbsan.M.loaded_segments (0x82a64 : word) = Some W_82a1c.
Proof. vm_refl. Qed.
Lemma D_82a1c : decode_any W_82a1c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a20 : bv 32 := 0x02813823.
Lemma F_82a20 : fetch_word AsanUbsan.M.loaded_segments (0x82a68 : word) = Some W_82a20.
Proof. vm_refl. Qed.
Lemma D_82a20 : decode_any W_82a20 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a24 : bv 32 := 0x02913423.
Lemma F_82a24 : fetch_word AsanUbsan.M.loaded_segments (0x82a6c : word) = Some W_82a24.
Proof. vm_refl. Qed.
Lemma D_82a24 : decode_any W_82a24 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a28 : bv 32 := 0x03213023.
Lemma F_82a28 : fetch_word AsanUbsan.M.loaded_segments (0x82a70 : word) = Some W_82a28.
Proof. vm_refl. Qed.
Lemma D_82a28 : decode_any W_82a28 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a2c : bv 32 := 0x01313c23.
Lemma F_82a2c : fetch_word AsanUbsan.M.loaded_segments (0x82a74 : word) = Some W_82a2c.
Proof. vm_refl. Qed.
Lemma D_82a2c : decode_any W_82a2c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a30 : bv 32 := 0x01413823.
Lemma F_82a30 : fetch_word AsanUbsan.M.loaded_segments (0x82a78 : word) = Some W_82a30.
Proof. vm_refl. Qed.
Lemma D_82a30 : decode_any W_82a30 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a34 : bv 32 := 0x01513423.
Lemma F_82a34 : fetch_word AsanUbsan.M.loaded_segments (0x82a7c : word) = Some W_82a34.
Proof. vm_refl. Qed.
Lemma D_82a34 : decode_any W_82a34 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a38 : bv 32 := 0x14058c63.
Lemma F_82a38 : fetch_word AsanUbsan.M.loaded_segments (0x82a80 : word) = Some W_82a38.
Proof. vm_refl. Qed.
Lemma D_82a38 : decode_any W_82a38 = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a3c : bv 32 := 0x00058493.
Lemma F_82a3c : fetch_word AsanUbsan.M.loaded_segments (0x82a84 : word) = Some W_82a3c.
Proof. vm_refl. Qed.
Lemma D_82a3c : decode_any W_82a3c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a40 : bv 32 := 0x00050413.
Lemma F_82a40 : fetch_word AsanUbsan.M.loaded_segments (0x82a88 : word) = Some W_82a40.
Proof. vm_refl. Qed.
Lemma D_82a40 : decode_any W_82a40 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a44 : bv 32 := 0x000d2517.
Lemma F_82a44 : fetch_word AsanUbsan.M.loaded_segments (0x82a8c : word) = Some W_82a44.
Proof. vm_refl. Qed.
Lemma D_82a44 : decode_any W_82a44 = Some (Auipc 10 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a48 : bv 32 := 0xa7453a83.
Lemma F_82a48 : fetch_word AsanUbsan.M.loaded_segments (0x82a90 : word) = Some W_82a48.
Proof. vm_refl. Qed.
Lemma D_82a48 : decode_any W_82a48 = Some (Load SZ8 true 21 10 2676, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a4c : bv 32 := 0x000ab583.
Lemma F_82a4c : fetch_word AsanUbsan.M.loaded_segments (0x82a94 : word) = Some W_82a4c.
Proof. vm_refl. Qed.
Lemma D_82a4c : decode_any W_82a4c = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a50 : bv 32 := 0xfff58513.
Lemma F_82a50 : fetch_word AsanUbsan.M.loaded_segments (0x82a98 : word) = Some W_82a50.
Proof. vm_refl. Qed.
Lemma D_82a50 : decode_any W_82a50 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a54 : bv 32 := 0x00a5b633.
Lemma F_82a54 : fetch_word AsanUbsan.M.loaded_segments (0x82a9c : word) = Some W_82a54.
Proof. vm_refl. Qed.
Lemma D_82a54 : decode_any W_82a54 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a58 : bv 32 := 0xfff60613.
Lemma F_82a58 : fetch_word AsanUbsan.M.loaded_segments (0x82aa0 : word) = Some W_82a58.
Proof. vm_refl. Qed.
Lemma D_82a58 : decode_any W_82a58 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a5c : bv 32 := 0x00a67633.
Lemma F_82a5c : fetch_word AsanUbsan.M.loaded_segments (0x82aa4 : word) = Some W_82a5c.
Proof. vm_refl. Qed.
Lemma D_82a5c : decode_any W_82a5c = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a60 : bv 32 := 0x04867263.
Lemma F_82a60 : fetch_word AsanUbsan.M.loaded_segments (0x82aa8 : word) = Some W_82a60.
Proof. vm_refl. Qed.
Lemma D_82a60 : decode_any W_82a60 = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a64 : bv 32 := 0x000d2697.
Lemma F_82a64 : fetch_word AsanUbsan.M.loaded_segments (0x82aac : word) = Some W_82a64.
Proof. vm_refl. Qed.
Lemma D_82a64 : decode_any W_82a64 = Some (Auipc 13 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a68 : bv 32 := 0xa5c6b683.
Lemma F_82a68 : fetch_word AsanUbsan.M.loaded_segments (0x82ab0 : word) = Some W_82a68.
Proof. vm_refl. Qed.
Lemma D_82a68 : decode_any W_82a68 = Some (Load SZ8 true 13 13 2652, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a6c : bv 32 := 0x000d2717.
Lemma F_82a6c : fetch_word AsanUbsan.M.loaded_segments (0x82ab4 : word) = Some W_82a6c.
Proof. vm_refl. Qed.
Lemma D_82a6c : decode_any W_82a6c = Some (Auipc 14 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a70 : bv 32 := 0xa5c73703.
Lemma F_82a70 : fetch_word AsanUbsan.M.loaded_segments (0x82ab8 : word) = Some W_82a70.
Proof. vm_refl. Qed.
Lemma D_82a70 : decode_any W_82a70 = Some (Load SZ8 true 14 14 2652, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a74 : bv 32 := 0x0006b803.
Lemma F_82a74 : fetch_word AsanUbsan.M.loaded_segments (0x82abc : word) = Some W_82a74.
Proof. vm_refl. Qed.
Lemma D_82a74 : decode_any W_82a74 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a78 : bv 32 := 0x00073683.
Lemma F_82a78 : fetch_word AsanUbsan.M.loaded_segments (0x82ac0 : word) = Some W_82a78.
Proof. vm_refl. Qed.
Lemma D_82a78 : decode_any W_82a78 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a7c : bv 32 := 0xfff80793.
Lemma F_82a7c : fetch_word AsanUbsan.M.loaded_segments (0x82ac4 : word) = Some W_82a7c.
Proof. vm_refl. Qed.
Lemma D_82a7c : decode_any W_82a7c = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a80 : bv 32 := 0x0087f463.
Lemma F_82a80 : fetch_word AsanUbsan.M.loaded_segments (0x82ac8 : word) = Some W_82a80.
Proof. vm_refl. Qed.
Lemma D_82a80 : decode_any W_82a80 = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a88 : bv 32 := 0x000d2717.
Lemma F_82a88 : fetch_word AsanUbsan.M.loaded_segments (0x82ad0 : word) = Some W_82a88.
Proof. vm_refl. Qed.
Lemma D_82a88 : decode_any W_82a88 = Some (Auipc 14 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a8c : bv 32 := 0xa4873703.
Lemma F_82a8c : fetch_word AsanUbsan.M.loaded_segments (0x82ad4 : word) = Some W_82a8c.
Proof. vm_refl. Qed.
Lemma D_82a8c : decode_any W_82a8c = Some (Load SZ8 true 14 14 2632, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a90 : bv 32 := 0x00073283.
Lemma F_82a90 : fetch_word AsanUbsan.M.loaded_segments (0x82ad8 : word) = Some W_82a90.
Proof. vm_refl. Qed.
Lemma D_82a90 : decode_any W_82a90 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a94 : bv 32 := 0x0032d713.
Lemma F_82a94 : fetch_word AsanUbsan.M.loaded_segments (0x82adc : word) = Some W_82a94.
Proof. vm_refl. Qed.
Lemma D_82a94 : decode_any W_82a94 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a98 : bv 32 := 0x00b708b3.
Lemma F_82a98 : fetch_word AsanUbsan.M.loaded_segments (0x82ae0 : word) = Some W_82a98.
Proof. vm_refl. Qed.
Lemma D_82a98 : decode_any W_82a98 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a9c : bv 32 := 0x1282e063.
Lemma F_82a9c : fetch_word AsanUbsan.M.loaded_segments (0x82ae4 : word) = Some W_82a9c.
Proof. vm_refl. Qed.
Lemma D_82a9c : decode_any W_82a9c = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aa0 : bv 32 := 0x1088fe63.
Lemma F_82aa0 : fetch_word AsanUbsan.M.loaded_segments (0x82ae8 : word) = Some W_82aa0.
Proof. vm_refl. Qed.
Lemma D_82aa0 : decode_any W_82aa0 = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aa4 : bv 32 := 0x00848933.
Lemma F_82aa4 : fetch_word AsanUbsan.M.loaded_segments (0x82aec : word) = Some W_82aa4.
Proof. vm_refl. Qed.
Lemma D_82aa4 : decode_any W_82aa4 = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aa8 : bv 32 := 0x05267263.
Lemma F_82aa8 : fetch_word AsanUbsan.M.loaded_segments (0x82af0 : word) = Some W_82aa8.
Proof. vm_refl. Qed.
Lemma D_82aa8 : decode_any W_82aa8 = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aac : bv 32 := 0x000d2617.
Lemma F_82aac : fetch_word AsanUbsan.M.loaded_segments (0x82af4 : word) = Some W_82aac.
Proof. vm_refl. Qed.
Lemma D_82aac : decode_any W_82aac = Some (Auipc 12 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ab0 : bv 32 := 0xa1463603.
Lemma F_82ab0 : fetch_word AsanUbsan.M.loaded_segments (0x82af8 : word) = Some W_82ab0.
Proof. vm_refl. Qed.
Lemma D_82ab0 : decode_any W_82ab0 = Some (Load SZ8 true 12 12 2580, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ab4 : bv 32 := 0x000d2697.
Lemma F_82ab4 : fetch_word AsanUbsan.M.loaded_segments (0x82afc : word) = Some W_82ab4.
Proof. vm_refl. Qed.
Lemma D_82ab4 : decode_any W_82ab4 = Some (Auipc 13 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ab8 : bv 32 := 0xa146b683.
Lemma F_82ab8 : fetch_word AsanUbsan.M.loaded_segments (0x82b00 : word) = Some W_82ab8.
Proof. vm_refl. Qed.
Lemma D_82ab8 : decode_any W_82ab8 = Some (Load SZ8 true 13 13 2580, 4%Z).
Proof. vm_refl. Qed.

Definition W_82abc : bv 32 := 0x00063783.
Lemma F_82abc : fetch_word AsanUbsan.M.loaded_segments (0x82b04 : word) = Some W_82abc.
Proof. vm_refl. Qed.
Lemma D_82abc : decode_any W_82abc = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ac0 : bv 32 := 0x0006b603.
Lemma F_82ac0 : fetch_word AsanUbsan.M.loaded_segments (0x82b08 : word) = Some W_82ac0.
Proof. vm_refl. Qed.
Lemma D_82ac0 : decode_any W_82ac0 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ac4 : bv 32 := 0xfff78713.
Lemma F_82ac4 : fetch_word AsanUbsan.M.loaded_segments (0x82b0c : word) = Some W_82ac4.
Proof. vm_refl. Qed.
Lemma D_82ac4 : decode_any W_82ac4 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ac8 : bv 32 := 0x01277463.
Lemma F_82ac8 : fetch_word AsanUbsan.M.loaded_segments (0x82b10 : word) = Some W_82ac8.
Proof. vm_refl. Qed.
Lemma D_82ac8 : decode_any W_82ac8 = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ad0 : bv 32 := 0x000d2697.
Lemma F_82ad0 : fetch_word AsanUbsan.M.loaded_segments (0x82b18 : word) = Some W_82ad0.
Proof. vm_refl. Qed.
Lemma D_82ad0 : decode_any W_82ad0 = Some (Auipc 13 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ad4 : bv 32 := 0xa006b683.
Lemma F_82ad4 : fetch_word AsanUbsan.M.loaded_segments (0x82b1c : word) = Some W_82ad4.
Proof. vm_refl. Qed.
Lemma D_82ad4 : decode_any W_82ad4 = Some (Load SZ8 true 13 13 2560, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ad8 : bv 32 := 0x0006b883.
Lemma F_82ad8 : fetch_word AsanUbsan.M.loaded_segments (0x82b20 : word) = Some W_82ad8.
Proof. vm_refl. Qed.
Lemma D_82ad8 : decode_any W_82ad8 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82adc : bv 32 := 0x0038d693.
Lemma F_82adc : fetch_word AsanUbsan.M.loaded_segments (0x82b24 : word) = Some W_82adc.
Proof. vm_refl. Qed.
Lemma D_82adc : decode_any W_82adc = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ae0 : bv 32 := 0x00b68833.
Lemma F_82ae0 : fetch_word AsanUbsan.M.loaded_segments (0x82b28 : word) = Some W_82ae0.
Proof. vm_refl. Qed.
Lemma D_82ae0 : decode_any W_82ae0 = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ae4 : bv 32 := 0x1328e463.
Lemma F_82ae4 : fetch_word AsanUbsan.M.loaded_segments (0x82b2c : word) = Some W_82ae4.
Proof. vm_refl. Qed.
Lemma D_82ae4 : decode_any W_82ae4 = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ae8 : bv 32 := 0x13287263.
Lemma F_82ae8 : fetch_word AsanUbsan.M.loaded_segments (0x82b30 : word) = Some W_82ae8.
Proof. vm_refl. Qed.
Lemma D_82ae8 : decode_any W_82ae8 = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aec : bv 32 := 0x23247863.
Lemma F_82aec : fetch_word AsanUbsan.M.loaded_segments (0x82b34 : word) = Some W_82aec.
Proof. vm_refl. Qed.
Lemma D_82aec : decode_any W_82aec = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_82af0 : bv 32 := 0x00740513.
Lemma F_82af0 : fetch_word AsanUbsan.M.loaded_segments (0x82b38 : word) = Some W_82af0.
Proof. vm_refl. Qed.
Lemma D_82af0 : decode_any W_82af0 = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82af4 : bv 32 := 0xff857513.
Lemma F_82af4 : fetch_word AsanUbsan.M.loaded_segments (0x82b3c : word) = Some W_82af4.
Proof. vm_refl. Qed.
Lemma D_82af4 : decode_any W_82af4 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82af8 : bv 32 := 0xff897a13.
Lemma F_82af8 : fetch_word AsanUbsan.M.loaded_segments (0x82b40 : word) = Some W_82af8.
Proof. vm_refl. Qed.
Lemma D_82af8 : decode_any W_82af8 = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82afc : bv 32 := 0xa91ff0ef.
Lemma F_82afc : fetch_word AsanUbsan.M.loaded_segments (0x82b44 : word) = Some W_82afc.
Proof. vm_refl. Qed.
Lemma D_82afc : decode_any W_82afc = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b00 : bv 32 := 0x00050993.
Lemma F_82b00 : fetch_word AsanUbsan.M.loaded_segments (0x82b48 : word) = Some W_82b00.
Proof. vm_refl. Qed.
Lemma D_82b00 : decode_any W_82b00 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b04 : bv 32 := 0x000a0513.
Lemma F_82b04 : fetch_word AsanUbsan.M.loaded_segments (0x82b4c : word) = Some W_82b04.
Proof. vm_refl. Qed.
Lemma D_82b04 : decode_any W_82b04 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b08 : bv 32 := 0xa85ff0ef.
Lemma F_82b08 : fetch_word AsanUbsan.M.loaded_segments (0x82b50 : word) = Some W_82b08.
Proof. vm_refl. Qed.
Lemma D_82b08 : decode_any W_82b08 = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b0c : bv 32 := 0x000ab583.
Lemma F_82b0c : fetch_word AsanUbsan.M.loaded_segments (0x82b54 : word) = Some W_82b0c.
Proof. vm_refl. Qed.
Lemma D_82b0c : decode_any W_82b0c = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b10 : bv 32 := 0x00345613.
Lemma F_82b10 : fetch_word AsanUbsan.M.loaded_segments (0x82b58 : word) = Some W_82b10.
Proof. vm_refl. Qed.
Lemma D_82b10 : decode_any W_82b10 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b14 : bv 32 := 0x00c58633.
Lemma F_82b14 : fetch_word AsanUbsan.M.loaded_segments (0x82b5c : word) = Some W_82b14.
Proof. vm_refl. Qed.
Lemma D_82b14 : decode_any W_82b14 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b18 : bv 32 := 0x00060603.
Lemma F_82b18 : fetch_word AsanUbsan.M.loaded_segments (0x82b60 : word) = Some W_82b18.
Proof. vm_refl. Qed.
Lemma D_82b18 : decode_any W_82b18 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b1c : bv 32 := 0x00060663.
Lemma F_82b1c : fetch_word AsanUbsan.M.loaded_segments (0x82b64 : word) = Some W_82b1c.
Proof. vm_refl. Qed.
Lemma D_82b1c : decode_any W_82b1c = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b20 : bv 32 := 0x00747693.
Lemma F_82b20 : fetch_word AsanUbsan.M.loaded_segments (0x82b68 : word) = Some W_82b20.
Proof. vm_refl. Qed.
Lemma D_82b20 : decode_any W_82b20 = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b24 : bv 32 := 0x02c6d063.
Lemma F_82b24 : fetch_word AsanUbsan.M.loaded_segments (0x82b6c : word) = Some W_82b24.
Proof. vm_refl. Qed.
Lemma D_82b24 : decode_any W_82b24 = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b28 : bv 32 := 0xfff90913.
Lemma F_82b28 : fetch_word AsanUbsan.M.loaded_segments (0x82b70 : word) = Some W_82b28.
Proof. vm_refl. Qed.
Lemma D_82b28 : decode_any W_82b28 = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b2c : bv 32 := 0x00395613.
Lemma F_82b2c : fetch_word AsanUbsan.M.loaded_segments (0x82b74 : word) = Some W_82b2c.
Proof. vm_refl. Qed.
Lemma D_82b2c : decode_any W_82b2c = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b30 : bv 32 := 0x00c585b3.
Lemma F_82b30 : fetch_word AsanUbsan.M.loaded_segments (0x82b78 : word) = Some W_82b30.
Proof. vm_refl. Qed.
Lemma D_82b30 : decode_any W_82b30 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b34 : bv 32 := 0x00058583.
Lemma F_82b34 : fetch_word AsanUbsan.M.loaded_segments (0x82b7c : word) = Some W_82b34.
Proof. vm_refl. Qed.
Lemma D_82b34 : decode_any W_82b34 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b38 : bv 32 := 0x04058263.
Lemma F_82b38 : fetch_word AsanUbsan.M.loaded_segments (0x82b80 : word) = Some W_82b38.
Proof. vm_refl. Qed.
Lemma D_82b38 : decode_any W_82b38 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b3c : bv 32 := 0x00797613.
Lemma F_82b3c : fetch_word AsanUbsan.M.loaded_segments (0x82b84 : word) = Some W_82b3c.
Proof. vm_refl. Qed.
Lemma D_82b3c : decode_any W_82b3c = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b40 : bv 32 := 0x02b64e63.
Lemma F_82b40 : fetch_word AsanUbsan.M.loaded_segments (0x82b88 : word) = Some W_82b40.
Proof. vm_refl. Qed.
Lemma D_82b40 : decode_any W_82b40 = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b7c : bv 32 := 0x00a9fa63.
Lemma F_82b7c : fetch_word AsanUbsan.M.loaded_segments (0x82bc4 : word) = Some W_82b7c.
Proof. vm_refl. Qed.
Lemma D_82b7c : decode_any W_82b7c = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b80 : bv 32 := 0x413505b3.
Lemma F_82b80 : fetch_word AsanUbsan.M.loaded_segments (0x82bc8 : word) = Some W_82b80.
Proof. vm_refl. Qed.
Lemma D_82b80 : decode_any W_82b80 = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b84 : bv 32 := 0x00098513.
Lemma F_82b84 : fetch_word AsanUbsan.M.loaded_segments (0x82bcc : word) = Some W_82b84.
Proof. vm_refl. Qed.
Lemma D_82b84 : decode_any W_82b84 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b88 : bv 32 := 0x37c100ef.
Lemma F_82b88 : fetch_word AsanUbsan.M.loaded_segments (0x82bd0 : word) = Some W_82b88.
Proof. vm_refl. Qed.
Lemma D_82b88 : decode_any W_82b88 = Some (Jal 1 66428, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b8c : bv 32 := 0xfa050ce3.
Lemma F_82b8c : fetch_word AsanUbsan.M.loaded_segments (0x82bd4 : word) = Some W_82b8c.
Proof. vm_refl. Qed.
Lemma D_82b8c : decode_any W_82b8c = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b90 : bv 32 := 0x00000413.
Lemma F_82b90 : fetch_word AsanUbsan.M.loaded_segments (0x82bd8 : word) = Some W_82b90.
Proof. vm_refl. Qed.
Lemma D_82b90 : decode_any W_82b90 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b94 : bv 32 := 0x00040513.
Lemma F_82b94 : fetch_word AsanUbsan.M.loaded_segments (0x82bdc : word) = Some W_82b94.
Proof. vm_refl. Qed.
Lemma D_82b94 : decode_any W_82b94 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b98 : bv 32 := 0x03813083.
Lemma F_82b98 : fetch_word AsanUbsan.M.loaded_segments (0x82be0 : word) = Some W_82b98.
Proof. vm_refl. Qed.
Lemma D_82b98 : decode_any W_82b98 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b9c : bv 32 := 0x03013403.
Lemma F_82b9c : fetch_word AsanUbsan.M.loaded_segments (0x82be4 : word) = Some W_82b9c.
Proof. vm_refl. Qed.
Lemma D_82b9c : decode_any W_82b9c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ba0 : bv 32 := 0x02813483.
Lemma F_82ba0 : fetch_word AsanUbsan.M.loaded_segments (0x82be8 : word) = Some W_82ba0.
Proof. vm_refl. Qed.
Lemma D_82ba0 : decode_any W_82ba0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ba4 : bv 32 := 0x02013903.
Lemma F_82ba4 : fetch_word AsanUbsan.M.loaded_segments (0x82bec : word) = Some W_82ba4.
Proof. vm_refl. Qed.
Lemma D_82ba4 : decode_any W_82ba4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ba8 : bv 32 := 0x01813983.
Lemma F_82ba8 : fetch_word AsanUbsan.M.loaded_segments (0x82bf0 : word) = Some W_82ba8.
Proof. vm_refl. Qed.
Lemma D_82ba8 : decode_any W_82ba8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bac : bv 32 := 0x01013a03.
Lemma F_82bac : fetch_word AsanUbsan.M.loaded_segments (0x82bf4 : word) = Some W_82bac.
Proof. vm_refl. Qed.
Lemma D_82bac : decode_any W_82bac = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bb0 : bv 32 := 0x00813a83.
Lemma F_82bb0 : fetch_word AsanUbsan.M.loaded_segments (0x82bf8 : word) = Some W_82bb0.
Proof. vm_refl. Qed.
Lemma D_82bb0 : decode_any W_82bb0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bb4 : bv 32 := 0x04010113.
Lemma F_82bb4 : fetch_word AsanUbsan.M.loaded_segments (0x82bfc : word) = Some W_82bb4.
Proof. vm_refl. Qed.
Lemma D_82bb4 : decode_any W_82bb4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bb8 : bv 32 := 0x00008067.
Lemma F_82bb8 : fetch_word AsanUbsan.M.loaded_segments (0x82c00 : word) = Some W_82bb8.
Proof. vm_refl. Qed.
Lemma D_82bb8 : decode_any W_82bb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

