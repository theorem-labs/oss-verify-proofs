(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_86abc : bv 32 := 0xfd010113.
Lemma F_86abc : fetch_word AsanUbsan.M.loaded_segments (0x86b0c : word) = Some W_86abc.
Proof. vm_refl. Qed.
Lemma D_86abc : decode_any W_86abc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ac0 : bv 32 := 0x02113423.
Lemma F_86ac0 : fetch_word AsanUbsan.M.loaded_segments (0x86b10 : word) = Some W_86ac0.
Proof. vm_refl. Qed.
Lemma D_86ac0 : decode_any W_86ac0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ac4 : bv 32 := 0x02813023.
Lemma F_86ac4 : fetch_word AsanUbsan.M.loaded_segments (0x86b14 : word) = Some W_86ac4.
Proof. vm_refl. Qed.
Lemma D_86ac4 : decode_any W_86ac4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ac8 : bv 32 := 0x00913c23.
Lemma F_86ac8 : fetch_word AsanUbsan.M.loaded_segments (0x86b18 : word) = Some W_86ac8.
Proof. vm_refl. Qed.
Lemma D_86ac8 : decode_any W_86ac8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_86acc : bv 32 := 0x01213823.
Lemma F_86acc : fetch_word AsanUbsan.M.loaded_segments (0x86b1c : word) = Some W_86acc.
Proof. vm_refl. Qed.
Lemma D_86acc : decode_any W_86acc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ad0 : bv 32 := 0x01313423.
Lemma F_86ad0 : fetch_word AsanUbsan.M.loaded_segments (0x86b20 : word) = Some W_86ad0.
Proof. vm_refl. Qed.
Lemma D_86ad0 : decode_any W_86ad0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ad4 : bv 32 := 0x0014f517.
Lemma F_86ad4 : fetch_word AsanUbsan.M.loaded_segments (0x86b24 : word) = Some W_86ad4.
Proof. vm_refl. Qed.
Lemma D_86ad4 : decode_any W_86ad4 = Some (Auipc 10 335, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ad8 : bv 32 := 0x06450413.
Lemma F_86ad8 : fetch_word AsanUbsan.M.loaded_segments (0x86b28 : word) = Some W_86ad8.
Proof. vm_refl. Qed.
Lemma D_86ad8 : decode_any W_86ad8 = Some (OpImm ALU_ADD 8 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_86adc : bv 32 := 0x00040503.
Lemma F_86adc : fetch_word AsanUbsan.M.loaded_segments (0x86b2c : word) = Some W_86adc.
Proof. vm_refl. Qed.
Lemma D_86adc : decode_any W_86adc = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ae0 : bv 32 := 0x0230000f.
Lemma F_86ae0 : fetch_word AsanUbsan.M.loaded_segments (0x86b30 : word) = Some W_86ae0.
Proof. vm_refl. Qed.
Lemma D_86ae0 : decode_any W_86ae0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ae4 : bv 32 := 0x0e051e63.
Lemma F_86ae4 : fetch_word AsanUbsan.M.loaded_segments (0x86b34 : word) = Some W_86ae4.
Proof. vm_refl. Qed.
Lemma D_86ae4 : decode_any W_86ae4 = Some (Branch BC_NE 10 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ae8 : bv 32 := 0x00140513.
Lemma F_86ae8 : fetch_word AsanUbsan.M.loaded_segments (0x86b38 : word) = Some W_86ae8.
Proof. vm_refl. Qed.
Lemma D_86ae8 : decode_any W_86ae8 = Some (OpImm ALU_ADD 10 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86aec : bv 32 := 0x0ff00593.
Lemma F_86aec : fetch_word AsanUbsan.M.loaded_segments (0x86b3c : word) = Some W_86aec.
Proof. vm_refl. Qed.
Lemma D_86aec : decode_any W_86aec = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_86af0 : bv 32 := 0x00100613.
Lemma F_86af0 : fetch_word AsanUbsan.M.loaded_segments (0x86b40 : word) = Some W_86af0.
Proof. vm_refl. Qed.
Lemma D_86af0 : decode_any W_86af0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86af4 : bv 32 := 0xffc57693.
Lemma F_86af4 : fetch_word AsanUbsan.M.loaded_segments (0x86b44 : word) = Some W_86af4.
Proof. vm_refl. Qed.
Lemma D_86af4 : decode_any W_86af4 = Some (OpImm ALU_AND 13 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_86af8 : bv 32 := 0x00357713.
Lemma F_86af8 : fetch_word AsanUbsan.M.loaded_segments (0x86b48 : word) = Some W_86af8.
Proof. vm_refl. Qed.
Lemma D_86af8 : decode_any W_86af8 = Some (OpImm ALU_AND 14 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86afc : bv 32 := 0x00371713.
Lemma F_86afc : fetch_word AsanUbsan.M.loaded_segments (0x86b4c : word) = Some W_86afc.
Proof. vm_refl. Qed.
Lemma D_86afc : decode_any W_86afc = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b00 : bv 32 := 0x00e595bb.
Lemma F_86b00 : fetch_word AsanUbsan.M.loaded_segments (0x86b50 : word) = Some W_86b00.
Proof. vm_refl. Qed.
Lemma D_86b00 : decode_any W_86b00 = Some (Op32 ALU_SLL 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b04 : bv 32 := 0x00e6163b.
Lemma F_86b04 : fetch_word AsanUbsan.M.loaded_segments (0x86b54 : word) = Some W_86b04.
Proof. vm_refl. Qed.
Lemma D_86b04 : decode_any W_86b04 = Some (Op32 ALU_SLL 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b08 : bv 32 := 0x1406a7af.
Lemma F_86b08 : fetch_word AsanUbsan.M.loaded_segments (0x86b58 : word) = Some W_86b08.
Proof. vm_refl. Qed.
Lemma D_86b08 : decode_any W_86b08 = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b0c : bv 32 := 0x00060813.
Lemma F_86b0c : fetch_word AsanUbsan.M.loaded_segments (0x86b5c : word) = Some W_86b0c.
Proof. vm_refl. Qed.
Lemma D_86b0c : decode_any W_86b0c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b10 : bv 32 := 0x0107c833.
Lemma F_86b10 : fetch_word AsanUbsan.M.loaded_segments (0x86b60 : word) = Some W_86b10.
Proof. vm_refl. Qed.
Lemma D_86b10 : decode_any W_86b10 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b14 : bv 32 := 0x00b87833.
Lemma F_86b14 : fetch_word AsanUbsan.M.loaded_segments (0x86b64 : word) = Some W_86b14.
Proof. vm_refl. Qed.
Lemma D_86b14 : decode_any W_86b14 = Some (Op ALU_AND 16 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b18 : bv 32 := 0x0107c833.
Lemma F_86b18 : fetch_word AsanUbsan.M.loaded_segments (0x86b68 : word) = Some W_86b18.
Proof. vm_refl. Qed.
Lemma D_86b18 : decode_any W_86b18 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b1c : bv 32 := 0x1906a82f.
Lemma F_86b1c : fetch_word AsanUbsan.M.loaded_segments (0x86b6c : word) = Some W_86b1c.
Proof. vm_refl. Qed.
Lemma D_86b1c : decode_any W_86b1c = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b20 : bv 32 := 0xfe0814e3.
Lemma F_86b20 : fetch_word AsanUbsan.M.loaded_segments (0x86b70 : word) = Some W_86b20.
Proof. vm_refl. Qed.
Lemma D_86b20 : decode_any W_86b20 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b24 : bv 32 := 0x00e7d5bb.
Lemma F_86b24 : fetch_word AsanUbsan.M.loaded_segments (0x86b74 : word) = Some W_86b24.
Proof. vm_refl. Qed.
Lemma D_86b24 : decode_any W_86b24 = Some (Op32 ALU_SRL 11 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b28 : bv 32 := 0x0ff5f593.
Lemma F_86b28 : fetch_word AsanUbsan.M.loaded_segments (0x86b78 : word) = Some W_86b28.
Proof. vm_refl. Qed.
Lemma D_86b28 : decode_any W_86b28 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b2c : bv 32 := 0x0c059c63.
Lemma F_86b2c : fetch_word AsanUbsan.M.loaded_segments (0x86b7c : word) = Some W_86b2c.
Proof. vm_refl. Qed.
Lemma D_86b2c : decode_any W_86b2c = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b30 : bv 32 := 0x00040503.
Lemma F_86b30 : fetch_word AsanUbsan.M.loaded_segments (0x86b80 : word) = Some W_86b30.
Proof. vm_refl. Qed.
Lemma D_86b30 : decode_any W_86b30 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b34 : bv 32 := 0x0a051263.
Lemma F_86b34 : fetch_word AsanUbsan.M.loaded_segments (0x86b84 : word) = Some W_86b34.
Proof. vm_refl. Qed.
Lemma D_86b34 : decode_any W_86b34 = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b38 : bv 32 := 0x000c0517.
Lemma F_86b38 : fetch_word AsanUbsan.M.loaded_segments (0x86b88 : word) = Some W_86b38.
Proof. vm_refl. Qed.
Lemma D_86b38 : decode_any W_86b38 = Some (Auipc 10 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b3c : bv 32 := 0x000815b7.
Lemma F_86b3c : fetch_word AsanUbsan.M.loaded_segments (0x86b8c : word) = Some W_86b3c.
Proof. vm_refl. Qed.
Lemma D_86b3c : decode_any W_86b3c = Some (Lui 11 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b40 : bv 32 := 0x77850493.
Lemma F_86b40 : fetch_word AsanUbsan.M.loaded_segments (0x86b90 : word) = Some W_86b40.
Proof. vm_refl. Qed.
Lemma D_86b40 : decode_any W_86b40 = Some (OpImm ALU_ADD 9 10 1912, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b44 : bv 32 := 0x0085851b.
Lemma F_86b44 : fetch_word AsanUbsan.M.loaded_segments (0x86b94 : word) = Some W_86b44.
Proof. vm_refl. Qed.
Lemma D_86b44 : decode_any W_86b44 = Some (OpImm32 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b48 : bv 32 := 0x00a48533.
Lemma F_86b48 : fetch_word AsanUbsan.M.loaded_segments (0x86b98 : word) = Some W_86b48.
Proof. vm_refl. Qed.
Lemma D_86b48 : decode_any W_86b48 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b4c : bv 32 := 0x02800613.
Lemma F_86b4c : fetch_word AsanUbsan.M.loaded_segments (0x86b9c : word) = Some W_86b4c.
Proof. vm_refl. Qed.
Lemma D_86b4c : decode_any W_86b4c = Some (OpImm ALU_ADD 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b50 : bv 32 := 0x00000593.
Lemma F_86b50 : fetch_word AsanUbsan.M.loaded_segments (0x86ba0 : word) = Some W_86b50.
Proof. vm_refl. Qed.
Lemma D_86b50 : decode_any W_86b50 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b54 : bv 32 := 0x269050ef.
Lemma F_86b54 : fetch_word AsanUbsan.M.loaded_segments (0x86ba4 : word) = Some W_86b54.
Proof. vm_refl. Qed.
Lemma D_86b54 : decode_any W_86b54 = Some (Jal 1 23144, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b58 : bv 32 := 0x00048023.
Lemma F_86b58 : fetch_word AsanUbsan.M.loaded_segments (0x86ba8 : word) = Some W_86b58.
Proof. vm_refl. Qed.
Lemma D_86b58 : decode_any W_86b58 = Some (Store SZ1 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b5c : bv 32 := 0x00848513.
Lemma F_86b5c : fetch_word AsanUbsan.M.loaded_segments (0x86bac : word) = Some W_86b5c.
Proof. vm_refl. Qed.
Lemma D_86b5c : decode_any W_86b5c = Some (OpImm ALU_ADD 10 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b60 : bv 32 := 0x00040637.
Lemma F_86b60 : fetch_word AsanUbsan.M.loaded_segments (0x86bb0 : word) = Some W_86b60.
Proof. vm_refl. Qed.
Lemma D_86b60 : decode_any W_86b60 = Some (Lui 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b64 : bv 32 := 0x000409b7.
Lemma F_86b64 : fetch_word AsanUbsan.M.loaded_segments (0x86bb4 : word) = Some W_86b64.
Proof. vm_refl. Qed.
Lemma D_86b64 : decode_any W_86b64 = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b68 : bv 32 := 0x00000593.
Lemma F_86b68 : fetch_word AsanUbsan.M.loaded_segments (0x86bb8 : word) = Some W_86b68.
Proof. vm_refl. Qed.
Lemma D_86b68 : decode_any W_86b68 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b6c : bv 32 := 0x251050ef.
Lemma F_86b6c : fetch_word AsanUbsan.M.loaded_segments (0x86bbc : word) = Some W_86b6c.
Proof. vm_refl. Qed.
Lemma D_86b6c : decode_any W_86b6c = Some (Jal 1 23120, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b70 : bv 32 := 0x0409851b.
Lemma F_86b70 : fetch_word AsanUbsan.M.loaded_segments (0x86bc0 : word) = Some W_86b70.
Proof. vm_refl. Qed.
Lemma D_86b70 : decode_any W_86b70 = Some (OpImm32 10 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b74 : bv 32 := 0x00a48533.
Lemma F_86b74 : fetch_word AsanUbsan.M.loaded_segments (0x86bc4 : word) = Some W_86b74.
Proof. vm_refl. Qed.
Lemma D_86b74 : decode_any W_86b74 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b78 : bv 32 := 0x01b00613.
Lemma F_86b78 : fetch_word AsanUbsan.M.loaded_segments (0x86bc8 : word) = Some W_86b78.
Proof. vm_refl. Qed.
Lemma D_86b78 : decode_any W_86b78 = Some (OpImm ALU_ADD 12 0 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b7c : bv 32 := 0x00761613.
Lemma F_86b7c : fetch_word AsanUbsan.M.loaded_segments (0x86bcc : word) = Some W_86b7c.
Proof. vm_refl. Qed.
Lemma D_86b7c : decode_any W_86b7c = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b80 : bv 32 := 0x00000593.
Lemma F_86b80 : fetch_word AsanUbsan.M.loaded_segments (0x86bd0 : word) = Some W_86b80.
Proof. vm_refl. Qed.
Lemma D_86b80 : decode_any W_86b80 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b84 : bv 32 := 0x239050ef.
Lemma F_86b84 : fetch_word AsanUbsan.M.loaded_segments (0x86bd4 : word) = Some W_86b84.
Proof. vm_refl. Qed.
Lemma D_86b84 : decode_any W_86b84 = Some (Jal 1 23096, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b88 : bv 32 := 0x00041937.
Lemma F_86b88 : fetch_word AsanUbsan.M.loaded_segments (0x86bd8 : word) = Some W_86b88.
Proof. vm_refl. Qed.
Lemma D_86b88 : decode_any W_86b88 = Some (Lui 18 65, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b8c : bv 32 := 0xdc09051b.
Lemma F_86b8c : fetch_word AsanUbsan.M.loaded_segments (0x86bdc : word) = Some W_86b8c.
Proof. vm_refl. Qed.
Lemma D_86b8c : decode_any W_86b8c = Some (OpImm32 10 18 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b90 : bv 32 := 0x00a48533.
Lemma F_86b90 : fetch_word AsanUbsan.M.loaded_segments (0x86be0 : word) = Some W_86b90.
Proof. vm_refl. Qed.
Lemma D_86b90 : decode_any W_86b90 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b94 : bv 32 := 0x2489861b.
Lemma F_86b94 : fetch_word AsanUbsan.M.loaded_segments (0x86be4 : word) = Some W_86b94.
Proof. vm_refl. Qed.
Lemma D_86b94 : decode_any W_86b94 = Some (OpImm32 12 19 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b98 : bv 32 := 0x00000593.
Lemma F_86b98 : fetch_word AsanUbsan.M.loaded_segments (0x86be8 : word) = Some W_86b98.
Proof. vm_refl. Qed.
Lemma D_86b98 : decode_any W_86b98 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86b9c : bv 32 := 0x221050ef.
Lemma F_86b9c : fetch_word AsanUbsan.M.loaded_segments (0x86bec : word) = Some W_86b9c.
Proof. vm_refl. Qed.
Lemma D_86b9c : decode_any W_86b9c = Some (Jal 1 23072, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ba0 : bv 32 := 0x000b7517.
Lemma F_86ba0 : fetch_word AsanUbsan.M.loaded_segments (0x86bf0 : word) = Some W_86ba0.
Proof. vm_refl. Qed.
Lemma D_86ba0 : decode_any W_86ba0 = Some (Auipc 10 183, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ba4 : bv 32 := 0xcb853983.
Lemma F_86ba4 : fetch_word AsanUbsan.M.loaded_segments (0x86bf4 : word) = Some W_86ba4.
Proof. vm_refl. Qed.
Lemma D_86ba4 : decode_any W_86ba4 = Some (Load SZ8 true 19 10 3256, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ba8 : bv 32 := 0x0009b503.
Lemma F_86ba8 : fetch_word AsanUbsan.M.loaded_segments (0x86bf8 : word) = Some W_86ba8.
Proof. vm_refl. Qed.
Lemma D_86ba8 : decode_any W_86ba8 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bac : bv 32 := 0x00051663.
Lemma F_86bac : fetch_word AsanUbsan.M.loaded_segments (0x86bfc : word) = Some W_86bac.
Proof. vm_refl. Qed.
Lemma D_86bac : decode_any W_86bac = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bb8 : bv 32 := 0x012485b3.
Lemma F_86bb8 : fetch_word AsanUbsan.M.loaded_segments (0x86c08 : word) = Some W_86bb8.
Proof. vm_refl. Qed.
Lemma D_86bb8 : decode_any W_86bb8 = Some (Op ALU_ADD 11 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bbc : bv 32 := 0xdd09061b.
Lemma F_86bbc : fetch_word AsanUbsan.M.loaded_segments (0x86c0c : word) = Some W_86bbc.
Proof. vm_refl. Qed.
Lemma D_86bbc : decode_any W_86bbc = Some (OpImm32 12 18 3536, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bc0 : bv 32 := 0x00c48633.
Lemma F_86bc0 : fetch_word AsanUbsan.M.loaded_segments (0x86c10 : word) = Some W_86bc0.
Proof. vm_refl. Qed.
Lemma D_86bc0 : decode_any W_86bc0 = Some (Op ALU_ADD 12 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bc4 : bv 32 := 0x00100693.
Lemma F_86bc4 : fetch_word AsanUbsan.M.loaded_segments (0x86c14 : word) = Some W_86bc4.
Proof. vm_refl. Qed.
Lemma D_86bc4 : decode_any W_86bc4 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bc8 : bv 32 := 0xdca5b023.
Lemma F_86bc8 : fetch_word AsanUbsan.M.loaded_segments (0x86c18 : word) = Some W_86bc8.
Proof. vm_refl. Qed.
Lemma D_86bc8 : decode_any W_86bc8 = Some (Store SZ8 11 10 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bcc : bv 32 := 0xdcc5b423.
Lemma F_86bcc : fetch_word AsanUbsan.M.loaded_segments (0x86c1c : word) = Some W_86bcc.
Proof. vm_refl. Qed.
Lemma D_86bcc : decode_any W_86bcc = Some (Store SZ8 11 12 3528, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bd0 : bv 32 := 0x0310000f.
Lemma F_86bd0 : fetch_word AsanUbsan.M.loaded_segments (0x86c20 : word) = Some W_86bd0.
Proof. vm_refl. Qed.
Lemma D_86bd0 : decode_any W_86bd0 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bd4 : bv 32 := 0x00d40023.
Lemma F_86bd4 : fetch_word AsanUbsan.M.loaded_segments (0x86c24 : word) = Some W_86bd4.
Proof. vm_refl. Qed.
Lemma D_86bd4 : decode_any W_86bd4 = Some (Store SZ1 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bd8 : bv 32 := 0x0310000f.
Lemma F_86bd8 : fetch_word AsanUbsan.M.loaded_segments (0x86c28 : word) = Some W_86bd8.
Proof. vm_refl. Qed.
Lemma D_86bd8 : decode_any W_86bd8 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bdc : bv 32 := 0x000400a3.
Lemma F_86bdc : fetch_word AsanUbsan.M.loaded_segments (0x86c2c : word) = Some W_86bdc.
Proof. vm_refl. Qed.
Lemma D_86bdc : decode_any W_86bdc = Some (Store SZ1 8 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_86be0 : bv 32 := 0x000c0517.
Lemma F_86be0 : fetch_word AsanUbsan.M.loaded_segments (0x86c30 : word) = Some W_86be0.
Proof. vm_refl. Qed.
Lemma D_86be0 : decode_any W_86be0 = Some (Auipc 10 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_86be4 : bv 32 := 0x6d050513.
Lemma F_86be4 : fetch_word AsanUbsan.M.loaded_segments (0x86c34 : word) = Some W_86be4.
Proof. vm_refl. Qed.
Lemma D_86be4 : decode_any W_86be4 = Some (OpImm ALU_ADD 10 10 1744, 4%Z).
Proof. vm_refl. Qed.

Definition W_86be8 : bv 32 := 0x02813083.
Lemma F_86be8 : fetch_word AsanUbsan.M.loaded_segments (0x86c38 : word) = Some W_86be8.
Proof. vm_refl. Qed.
Lemma D_86be8 : decode_any W_86be8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bec : bv 32 := 0x02013403.
Lemma F_86bec : fetch_word AsanUbsan.M.loaded_segments (0x86c3c : word) = Some W_86bec.
Proof. vm_refl. Qed.
Lemma D_86bec : decode_any W_86bec = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bf0 : bv 32 := 0x01813483.
Lemma F_86bf0 : fetch_word AsanUbsan.M.loaded_segments (0x86c40 : word) = Some W_86bf0.
Proof. vm_refl. Qed.
Lemma D_86bf0 : decode_any W_86bf0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bf4 : bv 32 := 0x01013903.
Lemma F_86bf4 : fetch_word AsanUbsan.M.loaded_segments (0x86c44 : word) = Some W_86bf4.
Proof. vm_refl. Qed.
Lemma D_86bf4 : decode_any W_86bf4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bf8 : bv 32 := 0x00813983.
Lemma F_86bf8 : fetch_word AsanUbsan.M.loaded_segments (0x86c48 : word) = Some W_86bf8.
Proof. vm_refl. Qed.
Lemma D_86bf8 : decode_any W_86bf8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_86bfc : bv 32 := 0x03010113.
Lemma F_86bfc : fetch_word AsanUbsan.M.loaded_segments (0x86c4c : word) = Some W_86bfc.
Proof. vm_refl. Qed.
Lemma D_86bfc : decode_any W_86bfc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_86c00 : bv 32 := 0x00008067.
Lemma F_86c00 : fetch_word AsanUbsan.M.loaded_segments (0x86c50 : word) = Some W_86c00.
Proof. vm_refl. Qed.
Lemma D_86c00 : decode_any W_86c00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
