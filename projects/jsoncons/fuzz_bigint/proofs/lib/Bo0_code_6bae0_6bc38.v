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

Definition W_6bae0 : bv 32 := 0xfd010113.
Lemma F_6bae0 : fetch_word AsanUbsan.M.loaded_segments (0x6bae0 : word) = Some W_6bae0.
Proof. vm_refl. Qed.
Lemma D_6bae0 : decode_any W_6bae0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bae4 : bv 32 := 0x02113423.
Lemma F_6bae4 : fetch_word AsanUbsan.M.loaded_segments (0x6bae4 : word) = Some W_6bae4.
Proof. vm_refl. Qed.
Lemma D_6bae4 : decode_any W_6bae4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bae8 : bv 32 := 0x02813023.
Lemma F_6bae8 : fetch_word AsanUbsan.M.loaded_segments (0x6bae8 : word) = Some W_6bae8.
Proof. vm_refl. Qed.
Lemma D_6bae8 : decode_any W_6bae8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6baec : bv 32 := 0x00913c23.
Lemma F_6baec : fetch_word AsanUbsan.M.loaded_segments (0x6baec : word) = Some W_6baec.
Proof. vm_refl. Qed.
Lemma D_6baec : decode_any W_6baec = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6baf0 : bv 32 := 0x01213823.
Lemma F_6baf0 : fetch_word AsanUbsan.M.loaded_segments (0x6baf0 : word) = Some W_6baf0.
Proof. vm_refl. Qed.
Lemma D_6baf0 : decode_any W_6baf0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6baf4 : bv 32 := 0x01313423.
Lemma F_6baf4 : fetch_word AsanUbsan.M.loaded_segments (0x6baf4 : word) = Some W_6baf4.
Proof. vm_refl. Qed.
Lemma D_6baf4 : decode_any W_6baf4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6baf8 : bv 32 := 0x00102517.
Lemma F_6baf8 : fetch_word AsanUbsan.M.loaded_segments (0x6baf8 : word) = Some W_6baf8.
Proof. vm_refl. Qed.
Lemma D_6baf8 : decode_any W_6baf8 = Some (Auipc 10 258, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bafc : bv 32 := 0x6d050413.
Lemma F_6bafc : fetch_word AsanUbsan.M.loaded_segments (0x6bafc : word) = Some W_6bafc.
Proof. vm_refl. Qed.
Lemma D_6bafc : decode_any W_6bafc = Some (OpImm ALU_ADD 8 10 1744, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb00 : bv 32 := 0x00040503.
Lemma F_6bb00 : fetch_word AsanUbsan.M.loaded_segments (0x6bb00 : word) = Some W_6bb00.
Proof. vm_refl. Qed.
Lemma D_6bb00 : decode_any W_6bb00 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb04 : bv 32 := 0x0230000f.
Lemma F_6bb04 : fetch_word AsanUbsan.M.loaded_segments (0x6bb04 : word) = Some W_6bb04.
Proof. vm_refl. Qed.
Lemma D_6bb04 : decode_any W_6bb04 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb08 : bv 32 := 0x0e051e63.
Lemma F_6bb08 : fetch_word AsanUbsan.M.loaded_segments (0x6bb08 : word) = Some W_6bb08.
Proof. vm_refl. Qed.
Lemma D_6bb08 : decode_any W_6bb08 = Some (Branch BC_NE 10 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb0c : bv 32 := 0x00140513.
Lemma F_6bb0c : fetch_word AsanUbsan.M.loaded_segments (0x6bb0c : word) = Some W_6bb0c.
Proof. vm_refl. Qed.
Lemma D_6bb0c : decode_any W_6bb0c = Some (OpImm ALU_ADD 10 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb10 : bv 32 := 0x0ff00593.
Lemma F_6bb10 : fetch_word AsanUbsan.M.loaded_segments (0x6bb10 : word) = Some W_6bb10.
Proof. vm_refl. Qed.
Lemma D_6bb10 : decode_any W_6bb10 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb14 : bv 32 := 0x00100613.
Lemma F_6bb14 : fetch_word AsanUbsan.M.loaded_segments (0x6bb14 : word) = Some W_6bb14.
Proof. vm_refl. Qed.
Lemma D_6bb14 : decode_any W_6bb14 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb18 : bv 32 := 0xffc57693.
Lemma F_6bb18 : fetch_word AsanUbsan.M.loaded_segments (0x6bb18 : word) = Some W_6bb18.
Proof. vm_refl. Qed.
Lemma D_6bb18 : decode_any W_6bb18 = Some (OpImm ALU_AND 13 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb1c : bv 32 := 0x00357713.
Lemma F_6bb1c : fetch_word AsanUbsan.M.loaded_segments (0x6bb1c : word) = Some W_6bb1c.
Proof. vm_refl. Qed.
Lemma D_6bb1c : decode_any W_6bb1c = Some (OpImm ALU_AND 14 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb20 : bv 32 := 0x00371713.
Lemma F_6bb20 : fetch_word AsanUbsan.M.loaded_segments (0x6bb20 : word) = Some W_6bb20.
Proof. vm_refl. Qed.
Lemma D_6bb20 : decode_any W_6bb20 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb24 : bv 32 := 0x00e595bb.
Lemma F_6bb24 : fetch_word AsanUbsan.M.loaded_segments (0x6bb24 : word) = Some W_6bb24.
Proof. vm_refl. Qed.
Lemma D_6bb24 : decode_any W_6bb24 = Some (Op32 ALU_SLL 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb28 : bv 32 := 0x00e6163b.
Lemma F_6bb28 : fetch_word AsanUbsan.M.loaded_segments (0x6bb28 : word) = Some W_6bb28.
Proof. vm_refl. Qed.
Lemma D_6bb28 : decode_any W_6bb28 = Some (Op32 ALU_SLL 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb2c : bv 32 := 0x1406a7af.
Lemma F_6bb2c : fetch_word AsanUbsan.M.loaded_segments (0x6bb2c : word) = Some W_6bb2c.
Proof. vm_refl. Qed.
Lemma D_6bb2c : decode_any W_6bb2c = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb30 : bv 32 := 0x00060813.
Lemma F_6bb30 : fetch_word AsanUbsan.M.loaded_segments (0x6bb30 : word) = Some W_6bb30.
Proof. vm_refl. Qed.
Lemma D_6bb30 : decode_any W_6bb30 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb34 : bv 32 := 0x0107c833.
Lemma F_6bb34 : fetch_word AsanUbsan.M.loaded_segments (0x6bb34 : word) = Some W_6bb34.
Proof. vm_refl. Qed.
Lemma D_6bb34 : decode_any W_6bb34 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb38 : bv 32 := 0x00b87833.
Lemma F_6bb38 : fetch_word AsanUbsan.M.loaded_segments (0x6bb38 : word) = Some W_6bb38.
Proof. vm_refl. Qed.
Lemma D_6bb38 : decode_any W_6bb38 = Some (Op ALU_AND 16 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb3c : bv 32 := 0x0107c833.
Lemma F_6bb3c : fetch_word AsanUbsan.M.loaded_segments (0x6bb3c : word) = Some W_6bb3c.
Proof. vm_refl. Qed.
Lemma D_6bb3c : decode_any W_6bb3c = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb40 : bv 32 := 0x1906a82f.
Lemma F_6bb40 : fetch_word AsanUbsan.M.loaded_segments (0x6bb40 : word) = Some W_6bb40.
Proof. vm_refl. Qed.
Lemma D_6bb40 : decode_any W_6bb40 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb44 : bv 32 := 0xfe0814e3.
Lemma F_6bb44 : fetch_word AsanUbsan.M.loaded_segments (0x6bb44 : word) = Some W_6bb44.
Proof. vm_refl. Qed.
Lemma D_6bb44 : decode_any W_6bb44 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb48 : bv 32 := 0x00e7d5bb.
Lemma F_6bb48 : fetch_word AsanUbsan.M.loaded_segments (0x6bb48 : word) = Some W_6bb48.
Proof. vm_refl. Qed.
Lemma D_6bb48 : decode_any W_6bb48 = Some (Op32 ALU_SRL 11 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb4c : bv 32 := 0x0ff5f593.
Lemma F_6bb4c : fetch_word AsanUbsan.M.loaded_segments (0x6bb4c : word) = Some W_6bb4c.
Proof. vm_refl. Qed.
Lemma D_6bb4c : decode_any W_6bb4c = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb50 : bv 32 := 0x0c059c63.
Lemma F_6bb50 : fetch_word AsanUbsan.M.loaded_segments (0x6bb50 : word) = Some W_6bb50.
Proof. vm_refl. Qed.
Lemma D_6bb50 : decode_any W_6bb50 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb54 : bv 32 := 0x00040503.
Lemma F_6bb54 : fetch_word AsanUbsan.M.loaded_segments (0x6bb54 : word) = Some W_6bb54.
Proof. vm_refl. Qed.
Lemma D_6bb54 : decode_any W_6bb54 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb58 : bv 32 := 0x0a051263.
Lemma F_6bb58 : fetch_word AsanUbsan.M.loaded_segments (0x6bb58 : word) = Some W_6bb58.
Proof. vm_refl. Qed.
Lemma D_6bb58 : decode_any W_6bb58 = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb5c : bv 32 := 0x00074517.
Lemma F_6bb5c : fetch_word AsanUbsan.M.loaded_segments (0x6bb5c : word) = Some W_6bb5c.
Proof. vm_refl. Qed.
Lemma D_6bb5c : decode_any W_6bb5c = Some (Auipc 10 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb60 : bv 32 := 0x000815b7.
Lemma F_6bb60 : fetch_word AsanUbsan.M.loaded_segments (0x6bb60 : word) = Some W_6bb60.
Proof. vm_refl. Qed.
Lemma D_6bb60 : decode_any W_6bb60 = Some (Lui 11 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb64 : bv 32 := 0xde450493.
Lemma F_6bb64 : fetch_word AsanUbsan.M.loaded_segments (0x6bb64 : word) = Some W_6bb64.
Proof. vm_refl. Qed.
Lemma D_6bb64 : decode_any W_6bb64 = Some (OpImm ALU_ADD 9 10 3556, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb68 : bv 32 := 0x0085851b.
Lemma F_6bb68 : fetch_word AsanUbsan.M.loaded_segments (0x6bb68 : word) = Some W_6bb68.
Proof. vm_refl. Qed.
Lemma D_6bb68 : decode_any W_6bb68 = Some (OpImm32 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb6c : bv 32 := 0x00a48533.
Lemma F_6bb6c : fetch_word AsanUbsan.M.loaded_segments (0x6bb6c : word) = Some W_6bb6c.
Proof. vm_refl. Qed.
Lemma D_6bb6c : decode_any W_6bb6c = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb70 : bv 32 := 0x02800613.
Lemma F_6bb70 : fetch_word AsanUbsan.M.loaded_segments (0x6bb70 : word) = Some W_6bb70.
Proof. vm_refl. Qed.
Lemma D_6bb70 : decode_any W_6bb70 = Some (OpImm ALU_ADD 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb74 : bv 32 := 0x00000593.
Lemma F_6bb74 : fetch_word AsanUbsan.M.loaded_segments (0x6bb74 : word) = Some W_6bb74.
Proof. vm_refl. Qed.
Lemma D_6bb74 : decode_any W_6bb74 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb78 : bv 32 := 0x269050ef.
Lemma F_6bb78 : fetch_word AsanUbsan.M.loaded_segments (0x6bb78 : word) = Some W_6bb78.
Proof. vm_refl. Qed.
Lemma D_6bb78 : decode_any W_6bb78 = Some (Jal 1 23144, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb7c : bv 32 := 0x00048023.
Lemma F_6bb7c : fetch_word AsanUbsan.M.loaded_segments (0x6bb7c : word) = Some W_6bb7c.
Proof. vm_refl. Qed.
Lemma D_6bb7c : decode_any W_6bb7c = Some (Store SZ1 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb80 : bv 32 := 0x00848513.
Lemma F_6bb80 : fetch_word AsanUbsan.M.loaded_segments (0x6bb80 : word) = Some W_6bb80.
Proof. vm_refl. Qed.
Lemma D_6bb80 : decode_any W_6bb80 = Some (OpImm ALU_ADD 10 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb84 : bv 32 := 0x00040637.
Lemma F_6bb84 : fetch_word AsanUbsan.M.loaded_segments (0x6bb84 : word) = Some W_6bb84.
Proof. vm_refl. Qed.
Lemma D_6bb84 : decode_any W_6bb84 = Some (Lui 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb88 : bv 32 := 0x000409b7.
Lemma F_6bb88 : fetch_word AsanUbsan.M.loaded_segments (0x6bb88 : word) = Some W_6bb88.
Proof. vm_refl. Qed.
Lemma D_6bb88 : decode_any W_6bb88 = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb8c : bv 32 := 0x00000593.
Lemma F_6bb8c : fetch_word AsanUbsan.M.loaded_segments (0x6bb8c : word) = Some W_6bb8c.
Proof. vm_refl. Qed.
Lemma D_6bb8c : decode_any W_6bb8c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb90 : bv 32 := 0x251050ef.
Lemma F_6bb90 : fetch_word AsanUbsan.M.loaded_segments (0x6bb90 : word) = Some W_6bb90.
Proof. vm_refl. Qed.
Lemma D_6bb90 : decode_any W_6bb90 = Some (Jal 1 23120, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb94 : bv 32 := 0x0409851b.
Lemma F_6bb94 : fetch_word AsanUbsan.M.loaded_segments (0x6bb94 : word) = Some W_6bb94.
Proof. vm_refl. Qed.
Lemma D_6bb94 : decode_any W_6bb94 = Some (OpImm32 10 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb98 : bv 32 := 0x00a48533.
Lemma F_6bb98 : fetch_word AsanUbsan.M.loaded_segments (0x6bb98 : word) = Some W_6bb98.
Proof. vm_refl. Qed.
Lemma D_6bb98 : decode_any W_6bb98 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bb9c : bv 32 := 0x01b00613.
Lemma F_6bb9c : fetch_word AsanUbsan.M.loaded_segments (0x6bb9c : word) = Some W_6bb9c.
Proof. vm_refl. Qed.
Lemma D_6bb9c : decode_any W_6bb9c = Some (OpImm ALU_ADD 12 0 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bba0 : bv 32 := 0x00761613.
Lemma F_6bba0 : fetch_word AsanUbsan.M.loaded_segments (0x6bba0 : word) = Some W_6bba0.
Proof. vm_refl. Qed.
Lemma D_6bba0 : decode_any W_6bba0 = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bba4 : bv 32 := 0x00000593.
Lemma F_6bba4 : fetch_word AsanUbsan.M.loaded_segments (0x6bba4 : word) = Some W_6bba4.
Proof. vm_refl. Qed.
Lemma D_6bba4 : decode_any W_6bba4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bba8 : bv 32 := 0x239050ef.
Lemma F_6bba8 : fetch_word AsanUbsan.M.loaded_segments (0x6bba8 : word) = Some W_6bba8.
Proof. vm_refl. Qed.
Lemma D_6bba8 : decode_any W_6bba8 = Some (Jal 1 23096, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbac : bv 32 := 0x00041937.
Lemma F_6bbac : fetch_word AsanUbsan.M.loaded_segments (0x6bbac : word) = Some W_6bbac.
Proof. vm_refl. Qed.
Lemma D_6bbac : decode_any W_6bbac = Some (Lui 18 65, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbb0 : bv 32 := 0xdc09051b.
Lemma F_6bbb0 : fetch_word AsanUbsan.M.loaded_segments (0x6bbb0 : word) = Some W_6bbb0.
Proof. vm_refl. Qed.
Lemma D_6bbb0 : decode_any W_6bbb0 = Some (OpImm32 10 18 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbb4 : bv 32 := 0x00a48533.
Lemma F_6bbb4 : fetch_word AsanUbsan.M.loaded_segments (0x6bbb4 : word) = Some W_6bbb4.
Proof. vm_refl. Qed.
Lemma D_6bbb4 : decode_any W_6bbb4 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbb8 : bv 32 := 0x2489861b.
Lemma F_6bbb8 : fetch_word AsanUbsan.M.loaded_segments (0x6bbb8 : word) = Some W_6bbb8.
Proof. vm_refl. Qed.
Lemma D_6bbb8 : decode_any W_6bbb8 = Some (OpImm32 12 19 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbbc : bv 32 := 0x00000593.
Lemma F_6bbbc : fetch_word AsanUbsan.M.loaded_segments (0x6bbbc : word) = Some W_6bbbc.
Proof. vm_refl. Qed.
Lemma D_6bbbc : decode_any W_6bbbc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbc0 : bv 32 := 0x221050ef.
Lemma F_6bbc0 : fetch_word AsanUbsan.M.loaded_segments (0x6bbc0 : word) = Some W_6bbc0.
Proof. vm_refl. Qed.
Lemma D_6bbc0 : decode_any W_6bbc0 = Some (Jal 1 23072, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbc4 : bv 32 := 0x0006b517.
Lemma F_6bbc4 : fetch_word AsanUbsan.M.loaded_segments (0x6bbc4 : word) = Some W_6bbc4.
Proof. vm_refl. Qed.
Lemma D_6bbc4 : decode_any W_6bbc4 = Some (Auipc 10 107, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbc8 : bv 32 := 0x8e453983.
Lemma F_6bbc8 : fetch_word AsanUbsan.M.loaded_segments (0x6bbc8 : word) = Some W_6bbc8.
Proof. vm_refl. Qed.
Lemma D_6bbc8 : decode_any W_6bbc8 = Some (Load SZ8 true 19 10 2276, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbcc : bv 32 := 0x0009b503.
Lemma F_6bbcc : fetch_word AsanUbsan.M.loaded_segments (0x6bbcc : word) = Some W_6bbcc.
Proof. vm_refl. Qed.
Lemma D_6bbcc : decode_any W_6bbcc = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbd0 : bv 32 := 0x00051663.
Lemma F_6bbd0 : fetch_word AsanUbsan.M.loaded_segments (0x6bbd0 : word) = Some W_6bbd0.
Proof. vm_refl. Qed.
Lemma D_6bbd0 : decode_any W_6bbd0 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbd4 : bv 32 := 0x138070ef.
Lemma F_6bbd4 : fetch_word AsanUbsan.M.loaded_segments (0x6bbd4 : word) = Some W_6bbd4.
Proof. vm_refl. Qed.
Lemma D_6bbd4 : decode_any W_6bbd4 = Some (Jal 1 28984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbd8 : bv 32 := 0x00a9b023.
Lemma F_6bbd8 : fetch_word AsanUbsan.M.loaded_segments (0x6bbd8 : word) = Some W_6bbd8.
Proof. vm_refl. Qed.
Lemma D_6bbd8 : decode_any W_6bbd8 = Some (Store SZ8 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbdc : bv 32 := 0x012485b3.
Lemma F_6bbdc : fetch_word AsanUbsan.M.loaded_segments (0x6bbdc : word) = Some W_6bbdc.
Proof. vm_refl. Qed.
Lemma D_6bbdc : decode_any W_6bbdc = Some (Op ALU_ADD 11 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbe0 : bv 32 := 0xdd09061b.
Lemma F_6bbe0 : fetch_word AsanUbsan.M.loaded_segments (0x6bbe0 : word) = Some W_6bbe0.
Proof. vm_refl. Qed.
Lemma D_6bbe0 : decode_any W_6bbe0 = Some (OpImm32 12 18 3536, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbe4 : bv 32 := 0x00c48633.
Lemma F_6bbe4 : fetch_word AsanUbsan.M.loaded_segments (0x6bbe4 : word) = Some W_6bbe4.
Proof. vm_refl. Qed.
Lemma D_6bbe4 : decode_any W_6bbe4 = Some (Op ALU_ADD 12 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbe8 : bv 32 := 0x00100693.
Lemma F_6bbe8 : fetch_word AsanUbsan.M.loaded_segments (0x6bbe8 : word) = Some W_6bbe8.
Proof. vm_refl. Qed.
Lemma D_6bbe8 : decode_any W_6bbe8 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbec : bv 32 := 0xdca5b023.
Lemma F_6bbec : fetch_word AsanUbsan.M.loaded_segments (0x6bbec : word) = Some W_6bbec.
Proof. vm_refl. Qed.
Lemma D_6bbec : decode_any W_6bbec = Some (Store SZ8 11 10 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbf0 : bv 32 := 0xdcc5b423.
Lemma F_6bbf0 : fetch_word AsanUbsan.M.loaded_segments (0x6bbf0 : word) = Some W_6bbf0.
Proof. vm_refl. Qed.
Lemma D_6bbf0 : decode_any W_6bbf0 = Some (Store SZ8 11 12 3528, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbf4 : bv 32 := 0x0310000f.
Lemma F_6bbf4 : fetch_word AsanUbsan.M.loaded_segments (0x6bbf4 : word) = Some W_6bbf4.
Proof. vm_refl. Qed.
Lemma D_6bbf4 : decode_any W_6bbf4 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbf8 : bv 32 := 0x00d40023.
Lemma F_6bbf8 : fetch_word AsanUbsan.M.loaded_segments (0x6bbf8 : word) = Some W_6bbf8.
Proof. vm_refl. Qed.
Lemma D_6bbf8 : decode_any W_6bbf8 = Some (Store SZ1 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bbfc : bv 32 := 0x0310000f.
Lemma F_6bbfc : fetch_word AsanUbsan.M.loaded_segments (0x6bbfc : word) = Some W_6bbfc.
Proof. vm_refl. Qed.
Lemma D_6bbfc : decode_any W_6bbfc = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc00 : bv 32 := 0x000400a3.
Lemma F_6bc00 : fetch_word AsanUbsan.M.loaded_segments (0x6bc00 : word) = Some W_6bc00.
Proof. vm_refl. Qed.
Lemma D_6bc00 : decode_any W_6bc00 = Some (Store SZ1 8 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc04 : bv 32 := 0x00074517.
Lemma F_6bc04 : fetch_word AsanUbsan.M.loaded_segments (0x6bc04 : word) = Some W_6bc04.
Proof. vm_refl. Qed.
Lemma D_6bc04 : decode_any W_6bc04 = Some (Auipc 10 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc08 : bv 32 := 0xd3c50513.
Lemma F_6bc08 : fetch_word AsanUbsan.M.loaded_segments (0x6bc08 : word) = Some W_6bc08.
Proof. vm_refl. Qed.
Lemma D_6bc08 : decode_any W_6bc08 = Some (OpImm ALU_ADD 10 10 3388, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc0c : bv 32 := 0x02813083.
Lemma F_6bc0c : fetch_word AsanUbsan.M.loaded_segments (0x6bc0c : word) = Some W_6bc0c.
Proof. vm_refl. Qed.
Lemma D_6bc0c : decode_any W_6bc0c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc10 : bv 32 := 0x02013403.
Lemma F_6bc10 : fetch_word AsanUbsan.M.loaded_segments (0x6bc10 : word) = Some W_6bc10.
Proof. vm_refl. Qed.
Lemma D_6bc10 : decode_any W_6bc10 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc14 : bv 32 := 0x01813483.
Lemma F_6bc14 : fetch_word AsanUbsan.M.loaded_segments (0x6bc14 : word) = Some W_6bc14.
Proof. vm_refl. Qed.
Lemma D_6bc14 : decode_any W_6bc14 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc18 : bv 32 := 0x01013903.
Lemma F_6bc18 : fetch_word AsanUbsan.M.loaded_segments (0x6bc18 : word) = Some W_6bc18.
Proof. vm_refl. Qed.
Lemma D_6bc18 : decode_any W_6bc18 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc1c : bv 32 := 0x00813983.
Lemma F_6bc1c : fetch_word AsanUbsan.M.loaded_segments (0x6bc1c : word) = Some W_6bc1c.
Proof. vm_refl. Qed.
Lemma D_6bc1c : decode_any W_6bc1c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc20 : bv 32 := 0x03010113.
Lemma F_6bc20 : fetch_word AsanUbsan.M.loaded_segments (0x6bc20 : word) = Some W_6bc20.
Proof. vm_refl. Qed.
Lemma D_6bc20 : decode_any W_6bc20 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc24 : bv 32 := 0x00008067.
Lemma F_6bc24 : fetch_word AsanUbsan.M.loaded_segments (0x6bc24 : word) = Some W_6bc24.
Proof. vm_refl. Qed.
Lemma D_6bc24 : decode_any W_6bc24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc28 : bv 32 := 0x734070ef.
Lemma F_6bc28 : fetch_word AsanUbsan.M.loaded_segments (0x6bc28 : word) = Some W_6bc28.
Proof. vm_refl. Qed.
Lemma D_6bc28 : decode_any W_6bc28 = Some (Jal 1 30516, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc2c : bv 32 := 0x00040503.
Lemma F_6bc2c : fetch_word AsanUbsan.M.loaded_segments (0x6bc2c : word) = Some W_6bc2c.
Proof. vm_refl. Qed.
Lemma D_6bc2c : decode_any W_6bc2c = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc30 : bv 32 := 0xfc0516e3.
Lemma F_6bc30 : fetch_word AsanUbsan.M.loaded_segments (0x6bc30 : word) = Some W_6bc30.
Proof. vm_refl. Qed.
Lemma D_6bc30 : decode_any W_6bc30 = Some (Branch BC_NE 10 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bc34 : bv 32 := 0xf29ff06f.
Lemma F_6bc34 : fetch_word AsanUbsan.M.loaded_segments (0x6bc34 : word) = Some W_6bc34.
Proof. vm_refl. Qed.
Lemma D_6bc34 : decode_any W_6bc34 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.
