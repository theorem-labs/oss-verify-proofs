(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_e3138 : bv 32 := 0x00459713.

Definition W_e313c : bv 32 := 0x40d60633.

Definition W_e3140 : bv 32 := 0x00d505b3.

Definition W_e3144 : bv 32 := 0x10070693.

Definition W_e3148 : bv 32 := 0xffc67713.

Definition W_e314c : bv 32 := 0x02d83633.

Definition W_e3150 : bv 32 := 0x00c5a023.

Definition W_e3154 : bv 32 := 0x00e586b3.

Definition W_e3158 : bv 32 := 0xfec6ae23.

Definition W_e315c : bv 32 := 0x08f76063.

Definition W_e3160 : bv 32 := 0x00c5a223.

Definition W_e3164 : bv 32 := 0x00c5a423.

Definition W_e3168 : bv 32 := 0x01900793.

Definition W_e316c : bv 32 := 0xfec6aa23.

Definition W_e3170 : bv 32 := 0xfec6ac23.

Definition W_e3174 : bv 32 := 0x06f76463.

Definition W_e3178 : bv 32 := 0x00c5a623.

Definition W_e317c : bv 32 := 0x00c5a823.

Definition W_e3180 : bv 32 := 0x00c5aa23.

Definition W_e3184 : bv 32 := 0x00c5ac23.

Definition W_e3188 : bv 32 := 0x0045f793.

Definition W_e318c : bv 32 := 0x02000813.

Definition W_e3190 : bv 32 := 0x01878793.

Definition W_e3194 : bv 32 := 0x40f70733.

Definition W_e3198 : bv 32 := 0xfec6a223.

Definition W_e319c : bv 32 := 0xfec6a423.

Definition W_e31a0 : bv 32 := 0xfec6a623.

Definition W_e31a4 : bv 32 := 0xfec6a823.

Definition W_e31a8 : bv 32 := 0x03076a63.

Definition W_e31ac : bv 32 := 0x02061613.

Definition W_e31b0 : bv 32 := 0x00f585b3.

Definition W_e31b4 : bv 32 := 0x02065693.

Definition W_e31b8 : bv 32 := 0x00d66633.

Definition W_e31bc : bv 32 := 0x01f00693.

Definition W_e31c0 : bv 32 := 0x00c5b023.

Definition W_e31c4 : bv 32 := 0x00c5b423.

Definition W_e31c8 : bv 32 := 0x00c5b823.

Definition W_e31cc : bv 32 := 0x00c5bc23.

Definition W_e31d0 : bv 32 := 0xfe070713.

Definition W_e31d4 : bv 32 := 0x02058593.

Definition W_e31d8 : bv 32 := 0xfee6e4e3.

Definition W_e31dc : bv 32 := 0x00008067.

Definition W_e3530 : bv 32 := 0xaa9ee0ef.

Definition W_e3534 : bv 32 := 0xfe010113.

Definition W_e3538 : bv 32 := 0x00113c23.

Definition W_e36bc : bv 32 := 0xfe010113.
Lemma F_e36bc : fetch_word Ubsan.M.loaded_segments (0xe36f0 : word) = Some W_e36bc.
Proof. vm_refl. Qed.
Lemma D_e36bc : decode_any W_e36bc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36c0 : bv 32 := 0x00113c23.
Lemma F_e36c0 : fetch_word Ubsan.M.loaded_segments (0xe36f4 : word) = Some W_e36c0.
Proof. vm_refl. Qed.
Lemma D_e36c0 : decode_any W_e36c0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36c4 : bv 32 := 0x00813823.
Lemma F_e36c4 : fetch_word Ubsan.M.loaded_segments (0xe36f8 : word) = Some W_e36c4.
Proof. vm_refl. Qed.
Lemma D_e36c4 : decode_any W_e36c4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36c8 : bv 32 := 0x00913423.
Lemma F_e36c8 : fetch_word Ubsan.M.loaded_segments (0xe36fc : word) = Some W_e36c8.
Proof. vm_refl. Qed.
Lemma D_e36c8 : decode_any W_e36c8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36cc : bv 32 := 0x00058413.
Lemma F_e36cc : fetch_word Ubsan.M.loaded_segments (0xe3700 : word) = Some W_e36cc.
Proof. vm_refl. Qed.
Lemma D_e36cc : decode_any W_e36cc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36d0 : bv 32 := 0x00050493.
Lemma F_e36d0 : fetch_word Ubsan.M.loaded_segments (0xe3704 : word) = Some W_e36d0.
Proof. vm_refl. Qed.
Lemma D_e36d0 : decode_any W_e36d0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36d4 : bv 32 := 0x00000593.
Lemma F_e36d4 : fetch_word Ubsan.M.loaded_segments (0xe3708 : word) = Some W_e36d4.
Proof. vm_refl. Qed.
Lemma D_e36d4 : decode_any W_e36d4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36d8 : bv 32 := 0x00040613.
Lemma F_e36d8 : fetch_word Ubsan.M.loaded_segments (0xe370c : word) = Some W_e36d8.
Proof. vm_refl. Qed.
Lemma D_e36d8 : decode_any W_e36d8 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36dc : bv 32 := 0xb90ff0ef.
Lemma F_e36dc : fetch_word Ubsan.M.loaded_segments (0xe3710 : word) = Some W_e36dc.
Proof. vm_refl. Qed.
Lemma D_e36dc : decode_any W_e36dc = Some (Jal 1 2093968, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36e0 : bv 32 := 0x00050463.
Lemma F_e36e0 : fetch_word Ubsan.M.loaded_segments (0xe3714 : word) = Some W_e36e0.
Proof. vm_refl. Qed.
Lemma D_e36e0 : decode_any W_e36e0 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36e4 : bv 32 := 0x40950433.
Lemma F_e36e4 : fetch_word Ubsan.M.loaded_segments (0xe3718 : word) = Some W_e36e4.
Proof. vm_refl. Qed.
Lemma D_e36e4 : decode_any W_e36e4 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36e8 : bv 32 := 0x00040513.
Lemma F_e36e8 : fetch_word Ubsan.M.loaded_segments (0xe371c : word) = Some W_e36e8.
Proof. vm_refl. Qed.
Lemma D_e36e8 : decode_any W_e36e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36ec : bv 32 := 0x01813083.
Lemma F_e36ec : fetch_word Ubsan.M.loaded_segments (0xe3720 : word) = Some W_e36ec.
Proof. vm_refl. Qed.
Lemma D_e36ec : decode_any W_e36ec = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36f0 : bv 32 := 0x01013403.
Lemma F_e36f0 : fetch_word Ubsan.M.loaded_segments (0xe3724 : word) = Some W_e36f0.
Proof. vm_refl. Qed.
Lemma D_e36f0 : decode_any W_e36f0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36f4 : bv 32 := 0x00813483.
Lemma F_e36f4 : fetch_word Ubsan.M.loaded_segments (0xe3728 : word) = Some W_e36f4.
Proof. vm_refl. Qed.
Lemma D_e36f4 : decode_any W_e36f4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36f8 : bv 32 := 0x02010113.
Lemma F_e36f8 : fetch_word Ubsan.M.loaded_segments (0xe372c : word) = Some W_e36f8.
Proof. vm_refl. Qed.
Lemma D_e36f8 : decode_any W_e36f8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_e36fc : bv 32 := 0x00008067.
Lemma F_e36fc : fetch_word Ubsan.M.loaded_segments (0xe3730 : word) = Some W_e36fc.
Proof. vm_refl. Qed.
Lemma D_e36fc : decode_any W_e36fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3b54 : bv 32 := 0x00050893.
Lemma F_e3b54 : fetch_word Ubsan.M.loaded_segments (0xe3b88 : word) = Some W_e3b54.
Proof. vm_refl. Qed.
Lemma D_e3b54 : decode_any W_e3b54 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3b58 : bv 32 := 0x00058513.
Lemma F_e3b58 : fetch_word Ubsan.M.loaded_segments (0xe3b8c : word) = Some W_e3b58.
Proof. vm_refl. Qed.
Lemma D_e3b58 : decode_any W_e3b58 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3b5c : bv 32 := 0x00060593.
Lemma F_e3b5c : fetch_word Ubsan.M.loaded_segments (0xe3b90 : word) = Some W_e3b5c.
Proof. vm_refl. Qed.
Lemma D_e3b5c : decode_any W_e3b5c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3b60 : bv 32 := 0x00068613.
Lemma F_e3b60 : fetch_word Ubsan.M.loaded_segments (0xe3b94 : word) = Some W_e3b60.
Proof. vm_refl. Qed.
Lemma D_e3b60 : decode_any W_e3b60 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3b64 : bv 32 := 0x00070693.
Lemma F_e3b64 : fetch_word Ubsan.M.loaded_segments (0xe3b98 : word) = Some W_e3b64.
Proof. vm_refl. Qed.
Lemma D_e3b64 : decode_any W_e3b64 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3b68 : bv 32 := 0x00078713.
Lemma F_e3b68 : fetch_word Ubsan.M.loaded_segments (0xe3b9c : word) = Some W_e3b68.
Proof. vm_refl. Qed.
Lemma D_e3b68 : decode_any W_e3b68 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3b6c : bv 32 := 0x00080793.
Lemma F_e3b6c : fetch_word Ubsan.M.loaded_segments (0xe3ba0 : word) = Some W_e3b6c.
Proof. vm_refl. Qed.
Lemma D_e3b6c : decode_any W_e3b6c = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3b70 : bv 32 := 0x00000073.
Lemma F_e3b70 : fetch_word Ubsan.M.loaded_segments (0xe3ba4 : word) = Some W_e3b70.
Proof. vm_refl. Qed.

Lemma E_e3b70 : is_ecall W_e3b70 = true.
Proof. reflexivity. Qed.

Definition W_e3b74 : bv 32 := 0x00008067.
Lemma F_e3b74 : fetch_word Ubsan.M.loaded_segments (0xe3ba8 : word) = Some W_e3b74.
Proof. vm_refl. Qed.
Lemma D_e3b74 : decode_any W_e3b74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3b78 : bv 32 := 0xfddff06f.
Lemma F_e3b78 : fetch_word Ubsan.M.loaded_segments (0xe3bac : word) = Some W_e3b78.
Proof. vm_refl. Qed.
Lemma D_e3b78 : decode_any W_e3b78 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.
