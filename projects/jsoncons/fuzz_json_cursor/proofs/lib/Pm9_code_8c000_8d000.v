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

Definition W_8ceb8 : bv 32 := 0xfd010113.
Lemma F_8ceb8 : fetch_word AsanUbsan.M.loaded_segments (0x8cf00 : word) = Some W_8ceb8.
Proof. vm_refl. Qed.
Lemma D_8ceb8 : decode_any W_8ceb8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cebc : bv 32 := 0x02113423.
Lemma F_8cebc : fetch_word AsanUbsan.M.loaded_segments (0x8cf04 : word) = Some W_8cebc.
Proof. vm_refl. Qed.
Lemma D_8cebc : decode_any W_8cebc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cec0 : bv 32 := 0x02813023.
Lemma F_8cec0 : fetch_word AsanUbsan.M.loaded_segments (0x8cf08 : word) = Some W_8cec0.
Proof. vm_refl. Qed.
Lemma D_8cec0 : decode_any W_8cec0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cec4 : bv 32 := 0x00913c23.
Lemma F_8cec4 : fetch_word AsanUbsan.M.loaded_segments (0x8cf0c : word) = Some W_8cec4.
Proof. vm_refl. Qed.
Lemma D_8cec4 : decode_any W_8cec4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cec8 : bv 32 := 0x01213823.
Lemma F_8cec8 : fetch_word AsanUbsan.M.loaded_segments (0x8cf10 : word) = Some W_8cec8.
Proof. vm_refl. Qed.
Lemma D_8cec8 : decode_any W_8cec8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cecc : bv 32 := 0x01313423.
Lemma F_8cecc : fetch_word AsanUbsan.M.loaded_segments (0x8cf14 : word) = Some W_8cecc.
Proof. vm_refl. Qed.
Lemma D_8cecc : decode_any W_8cecc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ced0 : bv 32 := 0x00161517.
Lemma F_8ced0 : fetch_word AsanUbsan.M.loaded_segments (0x8cf18 : word) = Some W_8ced0.
Proof. vm_refl. Qed.
Lemma D_8ced0 : decode_any W_8ced0 = Some (Auipc 10 353, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ced4 : bv 32 := 0x87050413.
Lemma F_8ced4 : fetch_word AsanUbsan.M.loaded_segments (0x8cf1c : word) = Some W_8ced4.
Proof. vm_refl. Qed.
Lemma D_8ced4 : decode_any W_8ced4 = Some (OpImm ALU_ADD 8 10 2160, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ced8 : bv 32 := 0x00040503.
Lemma F_8ced8 : fetch_word AsanUbsan.M.loaded_segments (0x8cf20 : word) = Some W_8ced8.
Proof. vm_refl. Qed.
Lemma D_8ced8 : decode_any W_8ced8 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cedc : bv 32 := 0x0230000f.
Lemma F_8cedc : fetch_word AsanUbsan.M.loaded_segments (0x8cf24 : word) = Some W_8cedc.
Proof. vm_refl. Qed.
Lemma D_8cedc : decode_any W_8cedc = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cee0 : bv 32 := 0x0e051e63.
Lemma F_8cee0 : fetch_word AsanUbsan.M.loaded_segments (0x8cf28 : word) = Some W_8cee0.
Proof. vm_refl. Qed.
Lemma D_8cee0 : decode_any W_8cee0 = Some (Branch BC_NE 10 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cee4 : bv 32 := 0x00140513.
Lemma F_8cee4 : fetch_word AsanUbsan.M.loaded_segments (0x8cf2c : word) = Some W_8cee4.
Proof. vm_refl. Qed.
Lemma D_8cee4 : decode_any W_8cee4 = Some (OpImm ALU_ADD 10 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cee8 : bv 32 := 0x0ff00593.
Lemma F_8cee8 : fetch_word AsanUbsan.M.loaded_segments (0x8cf30 : word) = Some W_8cee8.
Proof. vm_refl. Qed.
Lemma D_8cee8 : decode_any W_8cee8 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ceec : bv 32 := 0x00100613.
Lemma F_8ceec : fetch_word AsanUbsan.M.loaded_segments (0x8cf34 : word) = Some W_8ceec.
Proof. vm_refl. Qed.
Lemma D_8ceec : decode_any W_8ceec = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cef0 : bv 32 := 0xffc57693.
Lemma F_8cef0 : fetch_word AsanUbsan.M.loaded_segments (0x8cf38 : word) = Some W_8cef0.
Proof. vm_refl. Qed.
Lemma D_8cef0 : decode_any W_8cef0 = Some (OpImm ALU_AND 13 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cef4 : bv 32 := 0x00357713.
Lemma F_8cef4 : fetch_word AsanUbsan.M.loaded_segments (0x8cf3c : word) = Some W_8cef4.
Proof. vm_refl. Qed.
Lemma D_8cef4 : decode_any W_8cef4 = Some (OpImm ALU_AND 14 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cef8 : bv 32 := 0x00371713.
Lemma F_8cef8 : fetch_word AsanUbsan.M.loaded_segments (0x8cf40 : word) = Some W_8cef8.
Proof. vm_refl. Qed.
Lemma D_8cef8 : decode_any W_8cef8 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cefc : bv 32 := 0x00e595bb.
Lemma F_8cefc : fetch_word AsanUbsan.M.loaded_segments (0x8cf44 : word) = Some W_8cefc.
Proof. vm_refl. Qed.
Lemma D_8cefc : decode_any W_8cefc = Some (Op32 ALU_SLL 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf00 : bv 32 := 0x00e6163b.
Lemma F_8cf00 : fetch_word AsanUbsan.M.loaded_segments (0x8cf48 : word) = Some W_8cf00.
Proof. vm_refl. Qed.
Lemma D_8cf00 : decode_any W_8cf00 = Some (Op32 ALU_SLL 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf04 : bv 32 := 0x1406a7af.
Lemma F_8cf04 : fetch_word AsanUbsan.M.loaded_segments (0x8cf4c : word) = Some W_8cf04.
Proof. vm_refl. Qed.
Lemma D_8cf04 : decode_any W_8cf04 = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf08 : bv 32 := 0x00060813.
Lemma F_8cf08 : fetch_word AsanUbsan.M.loaded_segments (0x8cf50 : word) = Some W_8cf08.
Proof. vm_refl. Qed.
Lemma D_8cf08 : decode_any W_8cf08 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf0c : bv 32 := 0x0107c833.
Lemma F_8cf0c : fetch_word AsanUbsan.M.loaded_segments (0x8cf54 : word) = Some W_8cf0c.
Proof. vm_refl. Qed.
Lemma D_8cf0c : decode_any W_8cf0c = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf10 : bv 32 := 0x00b87833.
Lemma F_8cf10 : fetch_word AsanUbsan.M.loaded_segments (0x8cf58 : word) = Some W_8cf10.
Proof. vm_refl. Qed.
Lemma D_8cf10 : decode_any W_8cf10 = Some (Op ALU_AND 16 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf14 : bv 32 := 0x0107c833.
Lemma F_8cf14 : fetch_word AsanUbsan.M.loaded_segments (0x8cf5c : word) = Some W_8cf14.
Proof. vm_refl. Qed.
Lemma D_8cf14 : decode_any W_8cf14 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf18 : bv 32 := 0x1906a82f.
Lemma F_8cf18 : fetch_word AsanUbsan.M.loaded_segments (0x8cf60 : word) = Some W_8cf18.
Proof. vm_refl. Qed.
Lemma D_8cf18 : decode_any W_8cf18 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf1c : bv 32 := 0xfe0814e3.
Lemma F_8cf1c : fetch_word AsanUbsan.M.loaded_segments (0x8cf64 : word) = Some W_8cf1c.
Proof. vm_refl. Qed.
Lemma D_8cf1c : decode_any W_8cf1c = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf20 : bv 32 := 0x00e7d5bb.
Lemma F_8cf20 : fetch_word AsanUbsan.M.loaded_segments (0x8cf68 : word) = Some W_8cf20.
Proof. vm_refl. Qed.
Lemma D_8cf20 : decode_any W_8cf20 = Some (Op32 ALU_SRL 11 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf24 : bv 32 := 0x0ff5f593.
Lemma F_8cf24 : fetch_word AsanUbsan.M.loaded_segments (0x8cf6c : word) = Some W_8cf24.
Proof. vm_refl. Qed.
Lemma D_8cf24 : decode_any W_8cf24 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf28 : bv 32 := 0x0c059c63.
Lemma F_8cf28 : fetch_word AsanUbsan.M.loaded_segments (0x8cf70 : word) = Some W_8cf28.
Proof. vm_refl. Qed.
Lemma D_8cf28 : decode_any W_8cf28 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf2c : bv 32 := 0x00040503.
Lemma F_8cf2c : fetch_word AsanUbsan.M.loaded_segments (0x8cf74 : word) = Some W_8cf2c.
Proof. vm_refl. Qed.
Lemma D_8cf2c : decode_any W_8cf2c = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf30 : bv 32 := 0x0a051263.
Lemma F_8cf30 : fetch_word AsanUbsan.M.loaded_segments (0x8cf78 : word) = Some W_8cf30.
Proof. vm_refl. Qed.
Lemma D_8cf30 : decode_any W_8cf30 = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf34 : bv 32 := 0x000d2517.
Lemma F_8cf34 : fetch_word AsanUbsan.M.loaded_segments (0x8cf7c : word) = Some W_8cf34.
Proof. vm_refl. Qed.
Lemma D_8cf34 : decode_any W_8cf34 = Some (Auipc 10 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf38 : bv 32 := 0x000815b7.
Lemma F_8cf38 : fetch_word AsanUbsan.M.loaded_segments (0x8cf80 : word) = Some W_8cf38.
Proof. vm_refl. Qed.
Lemma D_8cf38 : decode_any W_8cf38 = Some (Lui 11 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf3c : bv 32 := 0xf8450493.
Lemma F_8cf3c : fetch_word AsanUbsan.M.loaded_segments (0x8cf84 : word) = Some W_8cf3c.
Proof. vm_refl. Qed.
Lemma D_8cf3c : decode_any W_8cf3c = Some (OpImm ALU_ADD 9 10 3972, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf40 : bv 32 := 0x0085851b.
Lemma F_8cf40 : fetch_word AsanUbsan.M.loaded_segments (0x8cf88 : word) = Some W_8cf40.
Proof. vm_refl. Qed.
Lemma D_8cf40 : decode_any W_8cf40 = Some (OpImm32 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf44 : bv 32 := 0x00a48533.
Lemma F_8cf44 : fetch_word AsanUbsan.M.loaded_segments (0x8cf8c : word) = Some W_8cf44.
Proof. vm_refl. Qed.
Lemma D_8cf44 : decode_any W_8cf44 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf48 : bv 32 := 0x02800613.
Lemma F_8cf48 : fetch_word AsanUbsan.M.loaded_segments (0x8cf90 : word) = Some W_8cf48.
Proof. vm_refl. Qed.
Lemma D_8cf48 : decode_any W_8cf48 = Some (OpImm ALU_ADD 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf4c : bv 32 := 0x00000593.
Lemma F_8cf4c : fetch_word AsanUbsan.M.loaded_segments (0x8cf94 : word) = Some W_8cf4c.
Proof. vm_refl. Qed.
Lemma D_8cf4c : decode_any W_8cf4c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf50 : bv 32 := 0x269050ef.
Lemma F_8cf50 : fetch_word AsanUbsan.M.loaded_segments (0x8cf98 : word) = Some W_8cf50.
Proof. vm_refl. Qed.
Lemma D_8cf50 : decode_any W_8cf50 = Some (Jal 1 23144, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf54 : bv 32 := 0x00048023.
Lemma F_8cf54 : fetch_word AsanUbsan.M.loaded_segments (0x8cf9c : word) = Some W_8cf54.
Proof. vm_refl. Qed.
Lemma D_8cf54 : decode_any W_8cf54 = Some (Store SZ1 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf58 : bv 32 := 0x00848513.
Lemma F_8cf58 : fetch_word AsanUbsan.M.loaded_segments (0x8cfa0 : word) = Some W_8cf58.
Proof. vm_refl. Qed.
Lemma D_8cf58 : decode_any W_8cf58 = Some (OpImm ALU_ADD 10 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf5c : bv 32 := 0x00040637.
Lemma F_8cf5c : fetch_word AsanUbsan.M.loaded_segments (0x8cfa4 : word) = Some W_8cf5c.
Proof. vm_refl. Qed.
Lemma D_8cf5c : decode_any W_8cf5c = Some (Lui 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf60 : bv 32 := 0x000409b7.
Lemma F_8cf60 : fetch_word AsanUbsan.M.loaded_segments (0x8cfa8 : word) = Some W_8cf60.
Proof. vm_refl. Qed.
Lemma D_8cf60 : decode_any W_8cf60 = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf64 : bv 32 := 0x00000593.
Lemma F_8cf64 : fetch_word AsanUbsan.M.loaded_segments (0x8cfac : word) = Some W_8cf64.
Proof. vm_refl. Qed.
Lemma D_8cf64 : decode_any W_8cf64 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf68 : bv 32 := 0x251050ef.
Lemma F_8cf68 : fetch_word AsanUbsan.M.loaded_segments (0x8cfb0 : word) = Some W_8cf68.
Proof. vm_refl. Qed.
Lemma D_8cf68 : decode_any W_8cf68 = Some (Jal 1 23120, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf6c : bv 32 := 0x0409851b.
Lemma F_8cf6c : fetch_word AsanUbsan.M.loaded_segments (0x8cfb4 : word) = Some W_8cf6c.
Proof. vm_refl. Qed.
Lemma D_8cf6c : decode_any W_8cf6c = Some (OpImm32 10 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf70 : bv 32 := 0x00a48533.
Lemma F_8cf70 : fetch_word AsanUbsan.M.loaded_segments (0x8cfb8 : word) = Some W_8cf70.
Proof. vm_refl. Qed.
Lemma D_8cf70 : decode_any W_8cf70 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf74 : bv 32 := 0x01b00613.
Lemma F_8cf74 : fetch_word AsanUbsan.M.loaded_segments (0x8cfbc : word) = Some W_8cf74.
Proof. vm_refl. Qed.
Lemma D_8cf74 : decode_any W_8cf74 = Some (OpImm ALU_ADD 12 0 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf78 : bv 32 := 0x00761613.
Lemma F_8cf78 : fetch_word AsanUbsan.M.loaded_segments (0x8cfc0 : word) = Some W_8cf78.
Proof. vm_refl. Qed.
Lemma D_8cf78 : decode_any W_8cf78 = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf7c : bv 32 := 0x00000593.
Lemma F_8cf7c : fetch_word AsanUbsan.M.loaded_segments (0x8cfc4 : word) = Some W_8cf7c.
Proof. vm_refl. Qed.
Lemma D_8cf7c : decode_any W_8cf7c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf80 : bv 32 := 0x239050ef.
Lemma F_8cf80 : fetch_word AsanUbsan.M.loaded_segments (0x8cfc8 : word) = Some W_8cf80.
Proof. vm_refl. Qed.
Lemma D_8cf80 : decode_any W_8cf80 = Some (Jal 1 23096, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf84 : bv 32 := 0x00041937.
Lemma F_8cf84 : fetch_word AsanUbsan.M.loaded_segments (0x8cfcc : word) = Some W_8cf84.
Proof. vm_refl. Qed.
Lemma D_8cf84 : decode_any W_8cf84 = Some (Lui 18 65, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf88 : bv 32 := 0xdc09051b.
Lemma F_8cf88 : fetch_word AsanUbsan.M.loaded_segments (0x8cfd0 : word) = Some W_8cf88.
Proof. vm_refl. Qed.
Lemma D_8cf88 : decode_any W_8cf88 = Some (OpImm32 10 18 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf8c : bv 32 := 0x00a48533.
Lemma F_8cf8c : fetch_word AsanUbsan.M.loaded_segments (0x8cfd4 : word) = Some W_8cf8c.
Proof. vm_refl. Qed.
Lemma D_8cf8c : decode_any W_8cf8c = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf90 : bv 32 := 0x2489861b.
Lemma F_8cf90 : fetch_word AsanUbsan.M.loaded_segments (0x8cfd8 : word) = Some W_8cf90.
Proof. vm_refl. Qed.
Lemma D_8cf90 : decode_any W_8cf90 = Some (OpImm32 12 19 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf94 : bv 32 := 0x00000593.
Lemma F_8cf94 : fetch_word AsanUbsan.M.loaded_segments (0x8cfdc : word) = Some W_8cf94.
Proof. vm_refl. Qed.
Lemma D_8cf94 : decode_any W_8cf94 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf98 : bv 32 := 0x221050ef.
Lemma F_8cf98 : fetch_word AsanUbsan.M.loaded_segments (0x8cfe0 : word) = Some W_8cf98.
Proof. vm_refl. Qed.
Lemma D_8cf98 : decode_any W_8cf98 = Some (Jal 1 23072, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cf9c : bv 32 := 0x000c7517.
Lemma F_8cf9c : fetch_word AsanUbsan.M.loaded_segments (0x8cfe4 : word) = Some W_8cf9c.
Proof. vm_refl. Qed.
Lemma D_8cf9c : decode_any W_8cf9c = Some (Auipc 10 199, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfa0 : bv 32 := 0x4fc53983.
Lemma F_8cfa0 : fetch_word AsanUbsan.M.loaded_segments (0x8cfe8 : word) = Some W_8cfa0.
Proof. vm_refl. Qed.
Lemma D_8cfa0 : decode_any W_8cfa0 = Some (Load SZ8 true 19 10 1276, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfa4 : bv 32 := 0x0009b503.
Lemma F_8cfa4 : fetch_word AsanUbsan.M.loaded_segments (0x8cfec : word) = Some W_8cfa4.
Proof. vm_refl. Qed.
Lemma D_8cfa4 : decode_any W_8cfa4 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfa8 : bv 32 := 0x00051663.
Lemma F_8cfa8 : fetch_word AsanUbsan.M.loaded_segments (0x8cff0 : word) = Some W_8cfa8.
Proof. vm_refl. Qed.
Lemma D_8cfa8 : decode_any W_8cfa8 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfb4 : bv 32 := 0x012485b3.
Lemma F_8cfb4 : fetch_word AsanUbsan.M.loaded_segments (0x8cffc : word) = Some W_8cfb4.
Proof. vm_refl. Qed.
Lemma D_8cfb4 : decode_any W_8cfb4 = Some (Op ALU_ADD 11 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfb8 : bv 32 := 0xdd09061b.
Lemma F_8cfb8 : fetch_word AsanUbsan.M.loaded_segments (0x8d000 : word) = Some W_8cfb8.
Proof. vm_refl. Qed.
Lemma D_8cfb8 : decode_any W_8cfb8 = Some (OpImm32 12 18 3536, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfbc : bv 32 := 0x00c48633.
Lemma F_8cfbc : fetch_word AsanUbsan.M.loaded_segments (0x8d004 : word) = Some W_8cfbc.
Proof. vm_refl. Qed.
Lemma D_8cfbc : decode_any W_8cfbc = Some (Op ALU_ADD 12 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfc0 : bv 32 := 0x00100693.
Lemma F_8cfc0 : fetch_word AsanUbsan.M.loaded_segments (0x8d008 : word) = Some W_8cfc0.
Proof. vm_refl. Qed.
Lemma D_8cfc0 : decode_any W_8cfc0 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfc4 : bv 32 := 0xdca5b023.
Lemma F_8cfc4 : fetch_word AsanUbsan.M.loaded_segments (0x8d00c : word) = Some W_8cfc4.
Proof. vm_refl. Qed.
Lemma D_8cfc4 : decode_any W_8cfc4 = Some (Store SZ8 11 10 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfc8 : bv 32 := 0xdcc5b423.
Lemma F_8cfc8 : fetch_word AsanUbsan.M.loaded_segments (0x8d010 : word) = Some W_8cfc8.
Proof. vm_refl. Qed.
Lemma D_8cfc8 : decode_any W_8cfc8 = Some (Store SZ8 11 12 3528, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfcc : bv 32 := 0x0310000f.
Lemma F_8cfcc : fetch_word AsanUbsan.M.loaded_segments (0x8d014 : word) = Some W_8cfcc.
Proof. vm_refl. Qed.
Lemma D_8cfcc : decode_any W_8cfcc = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfd0 : bv 32 := 0x00d40023.
Lemma F_8cfd0 : fetch_word AsanUbsan.M.loaded_segments (0x8d018 : word) = Some W_8cfd0.
Proof. vm_refl. Qed.
Lemma D_8cfd0 : decode_any W_8cfd0 = Some (Store SZ1 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfd4 : bv 32 := 0x0310000f.
Lemma F_8cfd4 : fetch_word AsanUbsan.M.loaded_segments (0x8d01c : word) = Some W_8cfd4.
Proof. vm_refl. Qed.
Lemma D_8cfd4 : decode_any W_8cfd4 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfd8 : bv 32 := 0x000400a3.
Lemma F_8cfd8 : fetch_word AsanUbsan.M.loaded_segments (0x8d020 : word) = Some W_8cfd8.
Proof. vm_refl. Qed.
Lemma D_8cfd8 : decode_any W_8cfd8 = Some (Store SZ1 8 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfdc : bv 32 := 0x000d2517.
Lemma F_8cfdc : fetch_word AsanUbsan.M.loaded_segments (0x8d024 : word) = Some W_8cfdc.
Proof. vm_refl. Qed.
Lemma D_8cfdc : decode_any W_8cfdc = Some (Auipc 10 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfe0 : bv 32 := 0xedc50513.
Lemma F_8cfe0 : fetch_word AsanUbsan.M.loaded_segments (0x8d028 : word) = Some W_8cfe0.
Proof. vm_refl. Qed.
Lemma D_8cfe0 : decode_any W_8cfe0 = Some (OpImm ALU_ADD 10 10 3804, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfe4 : bv 32 := 0x02813083.
Lemma F_8cfe4 : fetch_word AsanUbsan.M.loaded_segments (0x8d02c : word) = Some W_8cfe4.
Proof. vm_refl. Qed.
Lemma D_8cfe4 : decode_any W_8cfe4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfe8 : bv 32 := 0x02013403.
Lemma F_8cfe8 : fetch_word AsanUbsan.M.loaded_segments (0x8d030 : word) = Some W_8cfe8.
Proof. vm_refl. Qed.
Lemma D_8cfe8 : decode_any W_8cfe8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cfec : bv 32 := 0x01813483.
Lemma F_8cfec : fetch_word AsanUbsan.M.loaded_segments (0x8d034 : word) = Some W_8cfec.
Proof. vm_refl. Qed.
Lemma D_8cfec : decode_any W_8cfec = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cff0 : bv 32 := 0x01013903.
Lemma F_8cff0 : fetch_word AsanUbsan.M.loaded_segments (0x8d038 : word) = Some W_8cff0.
Proof. vm_refl. Qed.
Lemma D_8cff0 : decode_any W_8cff0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cff4 : bv 32 := 0x00813983.
Lemma F_8cff4 : fetch_word AsanUbsan.M.loaded_segments (0x8d03c : word) = Some W_8cff4.
Proof. vm_refl. Qed.
Lemma D_8cff4 : decode_any W_8cff4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cff8 : bv 32 := 0x03010113.
Lemma F_8cff8 : fetch_word AsanUbsan.M.loaded_segments (0x8d040 : word) = Some W_8cff8.
Proof. vm_refl. Qed.
Lemma D_8cff8 : decode_any W_8cff8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cffc : bv 32 := 0x00008067.
Lemma F_8cffc : fetch_word AsanUbsan.M.loaded_segments (0x8d044 : word) = Some W_8cffc.
Proof. vm_refl. Qed.
Lemma D_8cffc : decode_any W_8cffc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

