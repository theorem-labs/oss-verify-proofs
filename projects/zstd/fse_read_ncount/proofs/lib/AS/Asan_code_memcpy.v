(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.zstd.fse_read_ncount.images Require Import Asan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_92b0c : bv 32 := 0x0035f693.
Lemma F_92b0c : fetch_word Asan.M.loaded_segments (0x92ab0 : word) = Some W_92b0c.
Proof. vm_refl. Qed.
Lemma D_92b0c : decode_any W_92b0c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b10 : bv 32 := 0x10068863.
Lemma F_92b10 : fetch_word Asan.M.loaded_segments (0x92ab4 : word) = Some W_92b10.
Proof. vm_refl. Qed.
Lemma D_92b10 : decode_any W_92b10 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b14 : bv 32 := 0x02060e63.
Lemma F_92b14 : fetch_word Asan.M.loaded_segments (0x92ab8 : word) = Some W_92b14.
Proof. vm_refl. Qed.
Lemma D_92b14 : decode_any W_92b14 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b18 : bv 32 := 0x00158713.
Lemma F_92b18 : fetch_word Asan.M.loaded_segments (0x92abc : word) = Some W_92b18.
Proof. vm_refl. Qed.
Lemma D_92b18 : decode_any W_92b18 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b1c : bv 32 := 0x00100793.
Lemma F_92b1c : fetch_word Asan.M.loaded_segments (0x92ac0 : word) = Some W_92b1c.
Proof. vm_refl. Qed.
Lemma D_92b1c : decode_any W_92b1c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b20 : bv 32 := 0x00050693.
Lemma F_92b20 : fetch_word Asan.M.loaded_segments (0x92ac4 : word) = Some W_92b20.
Proof. vm_refl. Qed.
Lemma D_92b20 : decode_any W_92b20 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b24 : bv 32 := 0x0005c883.
Lemma F_92b24 : fetch_word Asan.M.loaded_segments (0x92ac8 : word) = Some W_92b24.
Proof. vm_refl. Qed.
Lemma D_92b24 : decode_any W_92b24 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b28 : bv 32 := 0x00060813.
Lemma F_92b28 : fetch_word Asan.M.loaded_segments (0x92acc : word) = Some W_92b28.
Proof. vm_refl. Qed.
Lemma D_92b28 : decode_any W_92b28 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b2c : bv 32 := 0x00158593.
Lemma F_92b2c : fetch_word Asan.M.loaded_segments (0x92ad0 : word) = Some W_92b2c.
Proof. vm_refl. Qed.
Lemma D_92b2c : decode_any W_92b2c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b30 : bv 32 := 0x00377293.
Lemma F_92b30 : fetch_word Asan.M.loaded_segments (0x92ad4 : word) = Some W_92b30.
Proof. vm_refl. Qed.
Lemma D_92b30 : decode_any W_92b30 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b34 : bv 32 := 0x01168023.
Lemma F_92b34 : fetch_word Asan.M.loaded_segments (0x92ad8 : word) = Some W_92b34.
Proof. vm_refl. Qed.
Lemma D_92b34 : decode_any W_92b34 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b38 : bv 32 := 0x00168693.
Lemma F_92b38 : fetch_word Asan.M.loaded_segments (0x92adc : word) = Some W_92b38.
Proof. vm_refl. Qed.
Lemma D_92b38 : decode_any W_92b38 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b3c : bv 32 := 0xfff60613.
Lemma F_92b3c : fetch_word Asan.M.loaded_segments (0x92ae0 : word) = Some W_92b3c.
Proof. vm_refl. Qed.
Lemma D_92b3c : decode_any W_92b3c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b40 : bv 32 := 0x00028a63.
Lemma F_92b40 : fetch_word Asan.M.loaded_segments (0x92ae4 : word) = Some W_92b40.
Proof. vm_refl. Qed.
Lemma D_92b40 : decode_any W_92b40 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b44 : bv 32 := 0x00170713.
Lemma F_92b44 : fetch_word Asan.M.loaded_segments (0x92ae8 : word) = Some W_92b44.
Proof. vm_refl. Qed.
Lemma D_92b44 : decode_any W_92b44 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b48 : bv 32 := 0xfcf81ee3.
Lemma F_92b48 : fetch_word Asan.M.loaded_segments (0x92aec : word) = Some W_92b48.
Proof. vm_refl. Qed.
Lemma D_92b48 : decode_any W_92b48 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b4c : bv 32 := 0x0080006f.
Lemma F_92b4c : fetch_word Asan.M.loaded_segments (0x92af0 : word) = Some W_92b4c.
Proof. vm_refl. Qed.
Lemma D_92b4c : decode_any W_92b4c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b50 : bv 32 := 0x00050693.
Lemma F_92b50 : fetch_word Asan.M.loaded_segments (0x92af4 : word) = Some W_92b50.
Proof. vm_refl. Qed.
Lemma D_92b50 : decode_any W_92b50 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b54 : bv 32 := 0x0036f793.
Lemma F_92b54 : fetch_word Asan.M.loaded_segments (0x92af8 : word) = Some W_92b54.
Proof. vm_refl. Qed.
Lemma D_92b54 : decode_any W_92b54 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b58 : bv 32 := 0x0c078a63.
Lemma F_92b58 : fetch_word Asan.M.loaded_segments (0x92afc : word) = Some W_92b58.
Proof. vm_refl. Qed.
Lemma D_92b58 : decode_any W_92b58 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b5c : bv 32 := 0x02000713.
Lemma F_92b5c : fetch_word Asan.M.loaded_segments (0x92b00 : word) = Some W_92b5c.
Proof. vm_refl. Qed.
Lemma D_92b5c : decode_any W_92b5c = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b60 : bv 32 := 0x02e67063.
Lemma F_92b60 : fetch_word Asan.M.loaded_segments (0x92b04 : word) = Some W_92b60.
Proof. vm_refl. Qed.
Lemma D_92b60 : decode_any W_92b60 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b64 : bv 32 := 0x01000713.
Lemma F_92b64 : fetch_word Asan.M.loaded_segments (0x92b08 : word) = Some W_92b64.
Proof. vm_refl. Qed.
Lemma D_92b64 : decode_any W_92b64 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b68 : bv 32 := 0x24e67863.
Lemma F_92b68 : fetch_word Asan.M.loaded_segments (0x92b0c : word) = Some W_92b68.
Proof. vm_refl. Qed.
Lemma D_92b68 : decode_any W_92b68 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b6c : bv 32 := 0x00867713.
Lemma F_92b6c : fetch_word Asan.M.loaded_segments (0x92b10 : word) = Some W_92b6c.
Proof. vm_refl. Qed.
Lemma D_92b6c : decode_any W_92b6c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b70 : bv 32 := 0x2c071e63.
Lemma F_92b70 : fetch_word Asan.M.loaded_segments (0x92b14 : word) = Some W_92b70.
Proof. vm_refl. Qed.
Lemma D_92b70 : decode_any W_92b70 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b74 : bv 32 := 0x00467713.
Lemma F_92b74 : fetch_word Asan.M.loaded_segments (0x92b18 : word) = Some W_92b74.
Proof. vm_refl. Qed.
Lemma D_92b74 : decode_any W_92b74 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b78 : bv 32 := 0x32071463.
Lemma F_92b78 : fetch_word Asan.M.loaded_segments (0x92b1c : word) = Some W_92b78.
Proof. vm_refl. Qed.
Lemma D_92b78 : decode_any W_92b78 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b7c : bv 32 := 0x3500006f.
Lemma F_92b7c : fetch_word Asan.M.loaded_segments (0x92b20 : word) = Some W_92b7c.
Proof. vm_refl. Qed.
Lemma D_92b7c : decode_any W_92b7c = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b80 : bv 32 := 0x0005a703.
Lemma F_92b80 : fetch_word Asan.M.loaded_segments (0x92b24 : word) = Some W_92b80.
Proof. vm_refl. Qed.
Lemma D_92b80 : decode_any W_92b80 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b84 : bv 32 := 0x00300813.
Lemma F_92b84 : fetch_word Asan.M.loaded_segments (0x92b28 : word) = Some W_92b84.
Proof. vm_refl. Qed.
Lemma D_92b84 : decode_any W_92b84 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b88 : bv 32 := 0x11078e63.
Lemma F_92b88 : fetch_word Asan.M.loaded_segments (0x92b2c : word) = Some W_92b88.
Proof. vm_refl. Qed.
Lemma D_92b88 : decode_any W_92b88 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b8c : bv 32 := 0x00200813.
Lemma F_92b8c : fetch_word Asan.M.loaded_segments (0x92b30 : word) = Some W_92b8c.
Proof. vm_refl. Qed.
Lemma D_92b8c : decode_any W_92b8c = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b90 : bv 32 := 0x19079c63.
Lemma F_92b90 : fetch_word Asan.M.loaded_segments (0x92b34 : word) = Some W_92b90.
Proof. vm_refl. Qed.
Lemma D_92b90 : decode_any W_92b90 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b94 : bv 32 := 0x00875793.
Lemma F_92b94 : fetch_word Asan.M.loaded_segments (0x92b38 : word) = Some W_92b94.
Proof. vm_refl. Qed.
Lemma D_92b94 : decode_any W_92b94 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b98 : bv 32 := 0xffe60613.
Lemma F_92b98 : fetch_word Asan.M.loaded_segments (0x92b3c : word) = Some W_92b98.
Proof. vm_refl. Qed.
Lemma D_92b98 : decode_any W_92b98 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.
Definition W_92b9c : bv 32 := 0x00e68023.
Lemma F_92b9c : fetch_word Asan.M.loaded_segments (0x92b40 : word) = Some W_92b9c.
Proof. vm_refl. Qed.
Lemma D_92b9c : decode_any W_92b9c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ba0 : bv 32 := 0x00f680a3.
Lemma F_92ba0 : fetch_word Asan.M.loaded_segments (0x92b44 : word) = Some W_92ba0.
Proof. vm_refl. Qed.
Lemma D_92ba0 : decode_any W_92ba0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ba4 : bv 32 := 0x00268693.
Lemma F_92ba4 : fetch_word Asan.M.loaded_segments (0x92b48 : word) = Some W_92ba4.
Proof. vm_refl. Qed.
Lemma D_92ba4 : decode_any W_92ba4 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ba8 : bv 32 := 0x01058593.
Lemma F_92ba8 : fetch_word Asan.M.loaded_segments (0x92b4c : word) = Some W_92ba8.
Proof. vm_refl. Qed.
Lemma D_92ba8 : decode_any W_92ba8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bac : bv 32 := 0x01100793.
Lemma F_92bac : fetch_word Asan.M.loaded_segments (0x92b50 : word) = Some W_92bac.
Proof. vm_refl. Qed.
Lemma D_92bac : decode_any W_92bac = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bb0 : bv 32 := 0x0107581b.
Lemma F_92bb0 : fetch_word Asan.M.loaded_segments (0x92b54 : word) = Some W_92bb0.
Proof. vm_refl. Qed.
Lemma D_92bb0 : decode_any W_92bb0 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bb4 : bv 32 := 0xff45a883.
Lemma F_92bb4 : fetch_word Asan.M.loaded_segments (0x92b58 : word) = Some W_92bb4.
Proof. vm_refl. Qed.
Lemma D_92bb4 : decode_any W_92bb4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bb8 : bv 32 := 0xff85a283.
Lemma F_92bb8 : fetch_word Asan.M.loaded_segments (0x92b5c : word) = Some W_92bb8.
Proof. vm_refl. Qed.
Lemma D_92bb8 : decode_any W_92bb8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bbc : bv 32 := 0xffc5a303.
Lemma F_92bbc : fetch_word Asan.M.loaded_segments (0x92b60 : word) = Some W_92bbc.
Proof. vm_refl. Qed.
Lemma D_92bbc : decode_any W_92bbc = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bc0 : bv 32 := 0x0005a703.
Lemma F_92bc0 : fetch_word Asan.M.loaded_segments (0x92b64 : word) = Some W_92bc0.
Proof. vm_refl. Qed.
Lemma D_92bc0 : decode_any W_92bc0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bc4 : bv 32 := 0x01089393.
Lemma F_92bc4 : fetch_word Asan.M.loaded_segments (0x92b68 : word) = Some W_92bc4.
Proof. vm_refl. Qed.
Lemma D_92bc4 : decode_any W_92bc4 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bc8 : bv 32 := 0x0108d89b.
Lemma F_92bc8 : fetch_word Asan.M.loaded_segments (0x92b6c : word) = Some W_92bc8.
Proof. vm_refl. Qed.
Lemma D_92bc8 : decode_any W_92bc8 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bcc : bv 32 := 0x0103e833.
Lemma F_92bcc : fetch_word Asan.M.loaded_segments (0x92b70 : word) = Some W_92bcc.
Proof. vm_refl. Qed.
Lemma D_92bcc : decode_any W_92bcc = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bd0 : bv 32 := 0x01029393.
Lemma F_92bd0 : fetch_word Asan.M.loaded_segments (0x92b74 : word) = Some W_92bd0.
Proof. vm_refl. Qed.
Lemma D_92bd0 : decode_any W_92bd0 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bd4 : bv 32 := 0x0102d29b.
Lemma F_92bd4 : fetch_word Asan.M.loaded_segments (0x92b78 : word) = Some W_92bd4.
Proof. vm_refl. Qed.
Lemma D_92bd4 : decode_any W_92bd4 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bd8 : bv 32 := 0x0113e8b3.
Lemma F_92bd8 : fetch_word Asan.M.loaded_segments (0x92b7c : word) = Some W_92bd8.
Proof. vm_refl. Qed.
Lemma D_92bd8 : decode_any W_92bd8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bdc : bv 32 := 0x01031393.
Lemma F_92bdc : fetch_word Asan.M.loaded_segments (0x92b80 : word) = Some W_92bdc.
Proof. vm_refl. Qed.
Lemma D_92bdc : decode_any W_92bdc = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92be0 : bv 32 := 0x0103531b.
Lemma F_92be0 : fetch_word Asan.M.loaded_segments (0x92b84 : word) = Some W_92be0.
Proof. vm_refl. Qed.
Lemma D_92be0 : decode_any W_92be0 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92be4 : bv 32 := 0x0053e2b3.
Lemma F_92be4 : fetch_word Asan.M.loaded_segments (0x92b88 : word) = Some W_92be4.
Proof. vm_refl. Qed.
Lemma D_92be4 : decode_any W_92be4 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_92be8 : bv 32 := 0x01071393.
Lemma F_92be8 : fetch_word Asan.M.loaded_segments (0x92b8c : word) = Some W_92be8.
Proof. vm_refl. Qed.
Lemma D_92be8 : decode_any W_92be8 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bec : bv 32 := 0x0063e333.
Lemma F_92bec : fetch_word Asan.M.loaded_segments (0x92b90 : word) = Some W_92bec.
Proof. vm_refl. Qed.
Lemma D_92bec : decode_any W_92bec = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bf0 : bv 32 := 0xff060613.
Lemma F_92bf0 : fetch_word Asan.M.loaded_segments (0x92b94 : word) = Some W_92bf0.
Proof. vm_refl. Qed.
Lemma D_92bf0 : decode_any W_92bf0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bf4 : bv 32 := 0x0106a023.
Lemma F_92bf4 : fetch_word Asan.M.loaded_segments (0x92b98 : word) = Some W_92bf4.
Proof. vm_refl. Qed.
Lemma D_92bf4 : decode_any W_92bf4 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bf8 : bv 32 := 0x0116a223.
Lemma F_92bf8 : fetch_word Asan.M.loaded_segments (0x92b9c : word) = Some W_92bf8.
Proof. vm_refl. Qed.
Lemma D_92bf8 : decode_any W_92bf8 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92bfc : bv 32 := 0x0056a423.
Lemma F_92bfc : fetch_word Asan.M.loaded_segments (0x92ba0 : word) = Some W_92bfc.
Proof. vm_refl. Qed.
Lemma D_92bfc : decode_any W_92bfc = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c00 : bv 32 := 0x0066a623.
Lemma F_92c00 : fetch_word Asan.M.loaded_segments (0x92ba4 : word) = Some W_92c00.
Proof. vm_refl. Qed.
Lemma D_92c00 : decode_any W_92c00 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c04 : bv 32 := 0x01068693.
Lemma F_92c04 : fetch_word Asan.M.loaded_segments (0x92ba8 : word) = Some W_92c04.
Proof. vm_refl. Qed.
Lemma D_92c04 : decode_any W_92c04 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c08 : bv 32 := 0x01058593.
Lemma F_92c08 : fetch_word Asan.M.loaded_segments (0x92bac : word) = Some W_92c08.
Proof. vm_refl. Qed.
Lemma D_92c08 : decode_any W_92c08 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c0c : bv 32 := 0xfac7e2e3.
Lemma F_92c0c : fetch_word Asan.M.loaded_segments (0x92bb0 : word) = Some W_92c0c.
Proof. vm_refl. Qed.
Lemma D_92c0c : decode_any W_92c0c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c10 : bv 32 := 0xff258593.
Lemma F_92c10 : fetch_word Asan.M.loaded_segments (0x92bb4 : word) = Some W_92c10.
Proof. vm_refl. Qed.
Lemma D_92c10 : decode_any W_92c10 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c14 : bv 32 := 0x01000713.
Lemma F_92c14 : fetch_word Asan.M.loaded_segments (0x92bb8 : word) = Some W_92c14.
Proof. vm_refl. Qed.
Lemma D_92c14 : decode_any W_92c14 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c18 : bv 32 := 0xf4e66ae3.
Lemma F_92c18 : fetch_word Asan.M.loaded_segments (0x92bbc : word) = Some W_92c18.
Proof. vm_refl. Qed.
Lemma D_92c18 : decode_any W_92c18 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c1c : bv 32 := 0x19c0006f.
Lemma F_92c1c : fetch_word Asan.M.loaded_segments (0x92bc0 : word) = Some W_92c1c.
Proof. vm_refl. Qed.
Lemma D_92c1c : decode_any W_92c1c = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c20 : bv 32 := 0x00050693.
Lemma F_92c20 : fetch_word Asan.M.loaded_segments (0x92bc4 : word) = Some W_92c20.
Proof. vm_refl. Qed.
Lemma D_92c20 : decode_any W_92c20 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c24 : bv 32 := 0x00357793.
Lemma F_92c24 : fetch_word Asan.M.loaded_segments (0x92bc8 : word) = Some W_92c24.
Proof. vm_refl. Qed.
Lemma D_92c24 : decode_any W_92c24 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c28 : bv 32 := 0xf2079ae3.
Lemma F_92c28 : fetch_word Asan.M.loaded_segments (0x92bcc : word) = Some W_92c28.
Proof. vm_refl. Qed.
Lemma D_92c28 : decode_any W_92c28 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c2c : bv 32 := 0x01000713.
Lemma F_92c2c : fetch_word Asan.M.loaded_segments (0x92bd0 : word) = Some W_92c2c.
Proof. vm_refl. Qed.
Lemma D_92c2c : decode_any W_92c2c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c30 : bv 32 := 0x02e66c63.
Lemma F_92c30 : fetch_word Asan.M.loaded_segments (0x92bd4 : word) = Some W_92c30.
Proof. vm_refl. Qed.
Lemma D_92c30 : decode_any W_92c30 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c34 : bv 32 := 0x00f00713.
Lemma F_92c34 : fetch_word Asan.M.loaded_segments (0x92bd8 : word) = Some W_92c34.
Proof. vm_refl. Qed.
Lemma D_92c34 : decode_any W_92c34 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c38 : bv 32 := 0x0005a783.
Lemma F_92c38 : fetch_word Asan.M.loaded_segments (0x92bdc : word) = Some W_92c38.
Proof. vm_refl. Qed.
Lemma D_92c38 : decode_any W_92c38 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c3c : bv 32 := 0x0045a803.
Lemma F_92c3c : fetch_word Asan.M.loaded_segments (0x92be0 : word) = Some W_92c3c.
Proof. vm_refl. Qed.
Lemma D_92c3c : decode_any W_92c3c = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c40 : bv 32 := 0x0085a883.
Lemma F_92c40 : fetch_word Asan.M.loaded_segments (0x92be4 : word) = Some W_92c40.
Proof. vm_refl. Qed.
Lemma D_92c40 : decode_any W_92c40 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c44 : bv 32 := 0x00c5a283.
Lemma F_92c44 : fetch_word Asan.M.loaded_segments (0x92be8 : word) = Some W_92c44.
Proof. vm_refl. Qed.
Lemma D_92c44 : decode_any W_92c44 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c48 : bv 32 := 0x01058593.
Lemma F_92c48 : fetch_word Asan.M.loaded_segments (0x92bec : word) = Some W_92c48.
Proof. vm_refl. Qed.
Lemma D_92c48 : decode_any W_92c48 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c4c : bv 32 := 0xff060613.
Lemma F_92c4c : fetch_word Asan.M.loaded_segments (0x92bf0 : word) = Some W_92c4c.
Proof. vm_refl. Qed.
Lemma D_92c4c : decode_any W_92c4c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c50 : bv 32 := 0x00f6a023.
Lemma F_92c50 : fetch_word Asan.M.loaded_segments (0x92bf4 : word) = Some W_92c50.
Proof. vm_refl. Qed.
Lemma D_92c50 : decode_any W_92c50 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c54 : bv 32 := 0x0106a223.
Lemma F_92c54 : fetch_word Asan.M.loaded_segments (0x92bf8 : word) = Some W_92c54.
Proof. vm_refl. Qed.
Lemma D_92c54 : decode_any W_92c54 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c58 : bv 32 := 0x0116a423.
Lemma F_92c58 : fetch_word Asan.M.loaded_segments (0x92bfc : word) = Some W_92c58.
Proof. vm_refl. Qed.
Lemma D_92c58 : decode_any W_92c58 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c5c : bv 32 := 0x0056a623.
Lemma F_92c5c : fetch_word Asan.M.loaded_segments (0x92c00 : word) = Some W_92c5c.
Proof. vm_refl. Qed.
Lemma D_92c5c : decode_any W_92c5c = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c60 : bv 32 := 0x01068693.
Lemma F_92c60 : fetch_word Asan.M.loaded_segments (0x92c04 : word) = Some W_92c60.
Proof. vm_refl. Qed.
Lemma D_92c60 : decode_any W_92c60 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c64 : bv 32 := 0xfcc76ae3.
Lemma F_92c64 : fetch_word Asan.M.loaded_segments (0x92c08 : word) = Some W_92c64.
Proof. vm_refl. Qed.
Lemma D_92c64 : decode_any W_92c64 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c68 : bv 32 := 0x00800713.
Lemma F_92c68 : fetch_word Asan.M.loaded_segments (0x92c0c : word) = Some W_92c68.
Proof. vm_refl. Qed.
Lemma D_92c68 : decode_any W_92c68 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c6c : bv 32 := 0x00e66e63.
Lemma F_92c6c : fetch_word Asan.M.loaded_segments (0x92c10 : word) = Some W_92c6c.
Proof. vm_refl. Qed.
Lemma D_92c6c : decode_any W_92c6c = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c70 : bv 32 := 0x0005a703.
Lemma F_92c70 : fetch_word Asan.M.loaded_segments (0x92c14 : word) = Some W_92c70.
Proof. vm_refl. Qed.
Lemma D_92c70 : decode_any W_92c70 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c74 : bv 32 := 0x0045a783.
Lemma F_92c74 : fetch_word Asan.M.loaded_segments (0x92c18 : word) = Some W_92c74.
Proof. vm_refl. Qed.
Lemma D_92c74 : decode_any W_92c74 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c78 : bv 32 := 0x00e6a023.
Lemma F_92c78 : fetch_word Asan.M.loaded_segments (0x92c1c : word) = Some W_92c78.
Proof. vm_refl. Qed.
Lemma D_92c78 : decode_any W_92c78 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c7c : bv 32 := 0x00f6a223.
Lemma F_92c7c : fetch_word Asan.M.loaded_segments (0x92c20 : word) = Some W_92c7c.
Proof. vm_refl. Qed.
Lemma D_92c7c : decode_any W_92c7c = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c80 : bv 32 := 0x00868693.
Lemma F_92c80 : fetch_word Asan.M.loaded_segments (0x92c24 : word) = Some W_92c80.
Proof. vm_refl. Qed.
Lemma D_92c80 : decode_any W_92c80 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c84 : bv 32 := 0x00858593.
Lemma F_92c84 : fetch_word Asan.M.loaded_segments (0x92c28 : word) = Some W_92c84.
Proof. vm_refl. Qed.
Lemma D_92c84 : decode_any W_92c84 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c88 : bv 32 := 0x00467713.
Lemma F_92c88 : fetch_word Asan.M.loaded_segments (0x92c2c : word) = Some W_92c88.
Proof. vm_refl. Qed.
Lemma D_92c88 : decode_any W_92c88 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c8c : bv 32 := 0x24070063.
Lemma F_92c8c : fetch_word Asan.M.loaded_segments (0x92c30 : word) = Some W_92c8c.
Proof. vm_refl. Qed.
Lemma D_92c8c : decode_any W_92c8c = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c90 : bv 32 := 0x0005a703.
Lemma F_92c90 : fetch_word Asan.M.loaded_segments (0x92c34 : word) = Some W_92c90.
Proof. vm_refl. Qed.
Lemma D_92c90 : decode_any W_92c90 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c94 : bv 32 := 0x00458593.
Lemma F_92c94 : fetch_word Asan.M.loaded_segments (0x92c38 : word) = Some W_92c94.
Proof. vm_refl. Qed.
Lemma D_92c94 : decode_any W_92c94 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c98 : bv 32 := 0x00e6a023.
Lemma F_92c98 : fetch_word Asan.M.loaded_segments (0x92c3c : word) = Some W_92c98.
Proof. vm_refl. Qed.
Lemma D_92c98 : decode_any W_92c98 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92c9c : bv 32 := 0x00468693.
Lemma F_92c9c : fetch_word Asan.M.loaded_segments (0x92c40 : word) = Some W_92c9c.
Proof. vm_refl. Qed.
Lemma D_92c9c : decode_any W_92c9c = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ca0 : bv 32 := 0x22c0006f.
Lemma F_92ca0 : fetch_word Asan.M.loaded_segments (0x92c44 : word) = Some W_92ca0.
Proof. vm_refl. Qed.
Lemma D_92ca0 : decode_any W_92ca0 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ca4 : bv 32 := 0x00e68023.
Lemma F_92ca4 : fetch_word Asan.M.loaded_segments (0x92c48 : word) = Some W_92ca4.
Proof. vm_refl. Qed.
Lemma D_92ca4 : decode_any W_92ca4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ca8 : bv 32 := 0x00168693.
Lemma F_92ca8 : fetch_word Asan.M.loaded_segments (0x92c4c : word) = Some W_92ca8.
Proof. vm_refl. Qed.
Lemma D_92ca8 : decode_any W_92ca8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cac : bv 32 := 0xfff60613.
Lemma F_92cac : fetch_word Asan.M.loaded_segments (0x92c50 : word) = Some W_92cac.
Proof. vm_refl. Qed.
Lemma D_92cac : decode_any W_92cac = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cb0 : bv 32 := 0x01058593.
Lemma F_92cb0 : fetch_word Asan.M.loaded_segments (0x92c54 : word) = Some W_92cb0.
Proof. vm_refl. Qed.
Lemma D_92cb0 : decode_any W_92cb0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cb4 : bv 32 := 0x01200793.
Lemma F_92cb4 : fetch_word Asan.M.loaded_segments (0x92c58 : word) = Some W_92cb4.
Proof. vm_refl. Qed.
Lemma D_92cb4 : decode_any W_92cb4 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cb8 : bv 32 := 0x0087581b.
Lemma F_92cb8 : fetch_word Asan.M.loaded_segments (0x92c5c : word) = Some W_92cb8.
Proof. vm_refl. Qed.
Lemma D_92cb8 : decode_any W_92cb8 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cbc : bv 32 := 0xff45a883.
Lemma F_92cbc : fetch_word Asan.M.loaded_segments (0x92c60 : word) = Some W_92cbc.
Proof. vm_refl. Qed.
Lemma D_92cbc : decode_any W_92cbc = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cc0 : bv 32 := 0xff85a283.
Lemma F_92cc0 : fetch_word Asan.M.loaded_segments (0x92c64 : word) = Some W_92cc0.
Proof. vm_refl. Qed.
Lemma D_92cc0 : decode_any W_92cc0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cc4 : bv 32 := 0xffc5a303.
Lemma F_92cc4 : fetch_word Asan.M.loaded_segments (0x92c68 : word) = Some W_92cc4.
Proof. vm_refl. Qed.
Lemma D_92cc4 : decode_any W_92cc4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cc8 : bv 32 := 0x0005a703.
Lemma F_92cc8 : fetch_word Asan.M.loaded_segments (0x92c6c : word) = Some W_92cc8.
Proof. vm_refl. Qed.
Lemma D_92cc8 : decode_any W_92cc8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ccc : bv 32 := 0x01889393.
Lemma F_92ccc : fetch_word Asan.M.loaded_segments (0x92c70 : word) = Some W_92ccc.
Proof. vm_refl. Qed.
Lemma D_92ccc : decode_any W_92ccc = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cd0 : bv 32 := 0x0088d89b.
Lemma F_92cd0 : fetch_word Asan.M.loaded_segments (0x92c74 : word) = Some W_92cd0.
Proof. vm_refl. Qed.
Lemma D_92cd0 : decode_any W_92cd0 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cd4 : bv 32 := 0x0103e833.
Lemma F_92cd4 : fetch_word Asan.M.loaded_segments (0x92c78 : word) = Some W_92cd4.
Proof. vm_refl. Qed.
Lemma D_92cd4 : decode_any W_92cd4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cd8 : bv 32 := 0x01829393.
Lemma F_92cd8 : fetch_word Asan.M.loaded_segments (0x92c7c : word) = Some W_92cd8.
Proof. vm_refl. Qed.
Lemma D_92cd8 : decode_any W_92cd8 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cdc : bv 32 := 0x0082d29b.
Lemma F_92cdc : fetch_word Asan.M.loaded_segments (0x92c80 : word) = Some W_92cdc.
Proof. vm_refl. Qed.
Lemma D_92cdc : decode_any W_92cdc = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ce0 : bv 32 := 0x0113e8b3.
Lemma F_92ce0 : fetch_word Asan.M.loaded_segments (0x92c84 : word) = Some W_92ce0.
Proof. vm_refl. Qed.
Lemma D_92ce0 : decode_any W_92ce0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ce4 : bv 32 := 0x01831393.
Lemma F_92ce4 : fetch_word Asan.M.loaded_segments (0x92c88 : word) = Some W_92ce4.
Proof. vm_refl. Qed.
Lemma D_92ce4 : decode_any W_92ce4 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ce8 : bv 32 := 0x0083531b.
Lemma F_92ce8 : fetch_word Asan.M.loaded_segments (0x92c8c : word) = Some W_92ce8.
Proof. vm_refl. Qed.
Lemma D_92ce8 : decode_any W_92ce8 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cec : bv 32 := 0x0053e2b3.
Lemma F_92cec : fetch_word Asan.M.loaded_segments (0x92c90 : word) = Some W_92cec.
Proof. vm_refl. Qed.
Lemma D_92cec : decode_any W_92cec = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cf0 : bv 32 := 0x01871393.
Lemma F_92cf0 : fetch_word Asan.M.loaded_segments (0x92c94 : word) = Some W_92cf0.
Proof. vm_refl. Qed.
Lemma D_92cf0 : decode_any W_92cf0 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cf4 : bv 32 := 0x0063e333.
Lemma F_92cf4 : fetch_word Asan.M.loaded_segments (0x92c98 : word) = Some W_92cf4.
Proof. vm_refl. Qed.
Lemma D_92cf4 : decode_any W_92cf4 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cf8 : bv 32 := 0xff060613.
Lemma F_92cf8 : fetch_word Asan.M.loaded_segments (0x92c9c : word) = Some W_92cf8.
Proof. vm_refl. Qed.
Lemma D_92cf8 : decode_any W_92cf8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_92cfc : bv 32 := 0x0106a023.
Lemma F_92cfc : fetch_word Asan.M.loaded_segments (0x92ca0 : word) = Some W_92cfc.
Proof. vm_refl. Qed.
Lemma D_92cfc : decode_any W_92cfc = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d00 : bv 32 := 0x0116a223.
Lemma F_92d00 : fetch_word Asan.M.loaded_segments (0x92ca4 : word) = Some W_92d00.
Proof. vm_refl. Qed.
Lemma D_92d00 : decode_any W_92d00 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d04 : bv 32 := 0x0056a423.
Lemma F_92d04 : fetch_word Asan.M.loaded_segments (0x92ca8 : word) = Some W_92d04.
Proof. vm_refl. Qed.
Lemma D_92d04 : decode_any W_92d04 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d08 : bv 32 := 0x0066a623.
Lemma F_92d08 : fetch_word Asan.M.loaded_segments (0x92cac : word) = Some W_92d08.
Proof. vm_refl. Qed.
Lemma D_92d08 : decode_any W_92d08 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d0c : bv 32 := 0x01068693.
Lemma F_92d0c : fetch_word Asan.M.loaded_segments (0x92cb0 : word) = Some W_92d0c.
Proof. vm_refl. Qed.
Lemma D_92d0c : decode_any W_92d0c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d10 : bv 32 := 0x01058593.
Lemma F_92d10 : fetch_word Asan.M.loaded_segments (0x92cb4 : word) = Some W_92d10.
Proof. vm_refl. Qed.
Lemma D_92d10 : decode_any W_92d10 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d14 : bv 32 := 0xfac7e2e3.
Lemma F_92d14 : fetch_word Asan.M.loaded_segments (0x92cb8 : word) = Some W_92d14.
Proof. vm_refl. Qed.
Lemma D_92d14 : decode_any W_92d14 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d18 : bv 32 := 0xff158593.
Lemma F_92d18 : fetch_word Asan.M.loaded_segments (0x92cbc : word) = Some W_92d18.
Proof. vm_refl. Qed.
Lemma D_92d18 : decode_any W_92d18 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d1c : bv 32 := 0x01000713.
Lemma F_92d1c : fetch_word Asan.M.loaded_segments (0x92cc0 : word) = Some W_92d1c.
Proof. vm_refl. Qed.
Lemma D_92d1c : decode_any W_92d1c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d20 : bv 32 := 0xe4e666e3.
Lemma F_92d20 : fetch_word Asan.M.loaded_segments (0x92cc4 : word) = Some W_92d20.
Proof. vm_refl. Qed.
Lemma D_92d20 : decode_any W_92d20 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d24 : bv 32 := 0x0940006f.
Lemma F_92d24 : fetch_word Asan.M.loaded_segments (0x92cc8 : word) = Some W_92d24.
Proof. vm_refl. Qed.
Lemma D_92d24 : decode_any W_92d24 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d28 : bv 32 := 0x00875793.
Lemma F_92d28 : fetch_word Asan.M.loaded_segments (0x92ccc : word) = Some W_92d28.
Proof. vm_refl. Qed.
Lemma D_92d28 : decode_any W_92d28 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d2c : bv 32 := 0x01075813.
Lemma F_92d2c : fetch_word Asan.M.loaded_segments (0x92cd0 : word) = Some W_92d2c.
Proof. vm_refl. Qed.
Lemma D_92d2c : decode_any W_92d2c = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d30 : bv 32 := 0xffd60613.
Lemma F_92d30 : fetch_word Asan.M.loaded_segments (0x92cd4 : word) = Some W_92d30.
Proof. vm_refl. Qed.
Lemma D_92d30 : decode_any W_92d30 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d34 : bv 32 := 0x00e68023.
Lemma F_92d34 : fetch_word Asan.M.loaded_segments (0x92cd8 : word) = Some W_92d34.
Proof. vm_refl. Qed.
Lemma D_92d34 : decode_any W_92d34 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d38 : bv 32 := 0x00f680a3.
Lemma F_92d38 : fetch_word Asan.M.loaded_segments (0x92cdc : word) = Some W_92d38.
Proof. vm_refl. Qed.
Lemma D_92d38 : decode_any W_92d38 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d3c : bv 32 := 0x01068123.
Lemma F_92d3c : fetch_word Asan.M.loaded_segments (0x92ce0 : word) = Some W_92d3c.
Proof. vm_refl. Qed.
Lemma D_92d3c : decode_any W_92d3c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d40 : bv 32 := 0x00368693.
Lemma F_92d40 : fetch_word Asan.M.loaded_segments (0x92ce4 : word) = Some W_92d40.
Proof. vm_refl. Qed.
Lemma D_92d40 : decode_any W_92d40 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d44 : bv 32 := 0x01058593.
Lemma F_92d44 : fetch_word Asan.M.loaded_segments (0x92ce8 : word) = Some W_92d44.
Proof. vm_refl. Qed.
Lemma D_92d44 : decode_any W_92d44 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d48 : bv 32 := 0x01000793.
Lemma F_92d48 : fetch_word Asan.M.loaded_segments (0x92cec : word) = Some W_92d48.
Proof. vm_refl. Qed.
Lemma D_92d48 : decode_any W_92d48 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d4c : bv 32 := 0x0187581b.
Lemma F_92d4c : fetch_word Asan.M.loaded_segments (0x92cf0 : word) = Some W_92d4c.
Proof. vm_refl. Qed.
Lemma D_92d4c : decode_any W_92d4c = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d50 : bv 32 := 0xff45a883.
Lemma F_92d50 : fetch_word Asan.M.loaded_segments (0x92cf4 : word) = Some W_92d50.
Proof. vm_refl. Qed.
Lemma D_92d50 : decode_any W_92d50 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d54 : bv 32 := 0xff85a283.
Lemma F_92d54 : fetch_word Asan.M.loaded_segments (0x92cf8 : word) = Some W_92d54.
Proof. vm_refl. Qed.
Lemma D_92d54 : decode_any W_92d54 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d58 : bv 32 := 0xffc5a303.
Lemma F_92d58 : fetch_word Asan.M.loaded_segments (0x92cfc : word) = Some W_92d58.
Proof. vm_refl. Qed.
Lemma D_92d58 : decode_any W_92d58 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d5c : bv 32 := 0x0005a703.
Lemma F_92d5c : fetch_word Asan.M.loaded_segments (0x92d00 : word) = Some W_92d5c.
Proof. vm_refl. Qed.
Lemma D_92d5c : decode_any W_92d5c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d60 : bv 32 := 0x00889393.
Lemma F_92d60 : fetch_word Asan.M.loaded_segments (0x92d04 : word) = Some W_92d60.
Proof. vm_refl. Qed.
Lemma D_92d60 : decode_any W_92d60 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d64 : bv 32 := 0x0188d89b.
Lemma F_92d64 : fetch_word Asan.M.loaded_segments (0x92d08 : word) = Some W_92d64.
Proof. vm_refl. Qed.
Lemma D_92d64 : decode_any W_92d64 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d68 : bv 32 := 0x0103e833.
Lemma F_92d68 : fetch_word Asan.M.loaded_segments (0x92d0c : word) = Some W_92d68.
Proof. vm_refl. Qed.
Lemma D_92d68 : decode_any W_92d68 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d6c : bv 32 := 0x00829393.
Lemma F_92d6c : fetch_word Asan.M.loaded_segments (0x92d10 : word) = Some W_92d6c.
Proof. vm_refl. Qed.
Lemma D_92d6c : decode_any W_92d6c = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d70 : bv 32 := 0x0182d29b.
Lemma F_92d70 : fetch_word Asan.M.loaded_segments (0x92d14 : word) = Some W_92d70.
Proof. vm_refl. Qed.
Lemma D_92d70 : decode_any W_92d70 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d74 : bv 32 := 0x0113e8b3.
Lemma F_92d74 : fetch_word Asan.M.loaded_segments (0x92d18 : word) = Some W_92d74.
Proof. vm_refl. Qed.
Lemma D_92d74 : decode_any W_92d74 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d78 : bv 32 := 0x00831393.
Lemma F_92d78 : fetch_word Asan.M.loaded_segments (0x92d1c : word) = Some W_92d78.
Proof. vm_refl. Qed.
Lemma D_92d78 : decode_any W_92d78 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d7c : bv 32 := 0x0183531b.
Lemma F_92d7c : fetch_word Asan.M.loaded_segments (0x92d20 : word) = Some W_92d7c.
Proof. vm_refl. Qed.
Lemma D_92d7c : decode_any W_92d7c = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d80 : bv 32 := 0x0053e2b3.
Lemma F_92d80 : fetch_word Asan.M.loaded_segments (0x92d24 : word) = Some W_92d80.
Proof. vm_refl. Qed.
Lemma D_92d80 : decode_any W_92d80 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d84 : bv 32 := 0x00871393.
Lemma F_92d84 : fetch_word Asan.M.loaded_segments (0x92d28 : word) = Some W_92d84.
Proof. vm_refl. Qed.
Lemma D_92d84 : decode_any W_92d84 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d88 : bv 32 := 0x0063e333.
Lemma F_92d88 : fetch_word Asan.M.loaded_segments (0x92d2c : word) = Some W_92d88.
Proof. vm_refl. Qed.
Lemma D_92d88 : decode_any W_92d88 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d8c : bv 32 := 0xff060613.
Lemma F_92d8c : fetch_word Asan.M.loaded_segments (0x92d30 : word) = Some W_92d8c.
Proof. vm_refl. Qed.
Lemma D_92d8c : decode_any W_92d8c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d90 : bv 32 := 0x0106a023.
Lemma F_92d90 : fetch_word Asan.M.loaded_segments (0x92d34 : word) = Some W_92d90.
Proof. vm_refl. Qed.
Lemma D_92d90 : decode_any W_92d90 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d94 : bv 32 := 0x0116a223.
Lemma F_92d94 : fetch_word Asan.M.loaded_segments (0x92d38 : word) = Some W_92d94.
Proof. vm_refl. Qed.
Lemma D_92d94 : decode_any W_92d94 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d98 : bv 32 := 0x0056a423.
Lemma F_92d98 : fetch_word Asan.M.loaded_segments (0x92d3c : word) = Some W_92d98.
Proof. vm_refl. Qed.
Lemma D_92d98 : decode_any W_92d98 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92d9c : bv 32 := 0x0066a623.
Lemma F_92d9c : fetch_word Asan.M.loaded_segments (0x92d40 : word) = Some W_92d9c.
Proof. vm_refl. Qed.
Lemma D_92d9c : decode_any W_92d9c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_92da0 : bv 32 := 0x01068693.
Lemma F_92da0 : fetch_word Asan.M.loaded_segments (0x92d44 : word) = Some W_92da0.
Proof. vm_refl. Qed.
Lemma D_92da0 : decode_any W_92da0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92da4 : bv 32 := 0x01058593.
Lemma F_92da4 : fetch_word Asan.M.loaded_segments (0x92d48 : word) = Some W_92da4.
Proof. vm_refl. Qed.
Lemma D_92da4 : decode_any W_92da4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92da8 : bv 32 := 0xfac7e2e3.
Lemma F_92da8 : fetch_word Asan.M.loaded_segments (0x92d4c : word) = Some W_92da8.
Proof. vm_refl. Qed.
Lemma D_92da8 : decode_any W_92da8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dac : bv 32 := 0xff358593.
Lemma F_92dac : fetch_word Asan.M.loaded_segments (0x92d50 : word) = Some W_92dac.
Proof. vm_refl. Qed.
Lemma D_92dac : decode_any W_92dac = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.
Definition W_92db0 : bv 32 := 0x01000713.
Lemma F_92db0 : fetch_word Asan.M.loaded_segments (0x92d54 : word) = Some W_92db0.
Proof. vm_refl. Qed.
Lemma D_92db0 : decode_any W_92db0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92db4 : bv 32 := 0xdae66ce3.
Lemma F_92db4 : fetch_word Asan.M.loaded_segments (0x92d58 : word) = Some W_92db4.
Proof. vm_refl. Qed.
Lemma D_92db4 : decode_any W_92db4 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.
Definition W_92db8 : bv 32 := 0x0005c703.
Lemma F_92db8 : fetch_word Asan.M.loaded_segments (0x92d5c : word) = Some W_92db8.
Proof. vm_refl. Qed.
Lemma D_92db8 : decode_any W_92db8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dbc : bv 32 := 0x0015c783.
Lemma F_92dbc : fetch_word Asan.M.loaded_segments (0x92d60 : word) = Some W_92dbc.
Proof. vm_refl. Qed.
Lemma D_92dbc : decode_any W_92dbc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dc0 : bv 32 := 0x0025c803.
Lemma F_92dc0 : fetch_word Asan.M.loaded_segments (0x92d64 : word) = Some W_92dc0.
Proof. vm_refl. Qed.
Lemma D_92dc0 : decode_any W_92dc0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dc4 : bv 32 := 0x0035c883.
Lemma F_92dc4 : fetch_word Asan.M.loaded_segments (0x92d68 : word) = Some W_92dc4.
Proof. vm_refl. Qed.
Lemma D_92dc4 : decode_any W_92dc4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dc8 : bv 32 := 0x0045c283.
Lemma F_92dc8 : fetch_word Asan.M.loaded_segments (0x92d6c : word) = Some W_92dc8.
Proof. vm_refl. Qed.
Lemma D_92dc8 : decode_any W_92dc8 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dcc : bv 32 := 0x0055c303.
Lemma F_92dcc : fetch_word Asan.M.loaded_segments (0x92d70 : word) = Some W_92dcc.
Proof. vm_refl. Qed.
Lemma D_92dcc : decode_any W_92dcc = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dd0 : bv 32 := 0x0065c383.
Lemma F_92dd0 : fetch_word Asan.M.loaded_segments (0x92d74 : word) = Some W_92dd0.
Proof. vm_refl. Qed.
Lemma D_92dd0 : decode_any W_92dd0 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dd4 : bv 32 := 0x0075ce03.
Lemma F_92dd4 : fetch_word Asan.M.loaded_segments (0x92d78 : word) = Some W_92dd4.
Proof. vm_refl. Qed.
Lemma D_92dd4 : decode_any W_92dd4 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dd8 : bv 32 := 0x00e68023.
Lemma F_92dd8 : fetch_word Asan.M.loaded_segments (0x92d7c : word) = Some W_92dd8.
Proof. vm_refl. Qed.
Lemma D_92dd8 : decode_any W_92dd8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ddc : bv 32 := 0x00f680a3.
Lemma F_92ddc : fetch_word Asan.M.loaded_segments (0x92d80 : word) = Some W_92ddc.
Proof. vm_refl. Qed.
Lemma D_92ddc : decode_any W_92ddc = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92de0 : bv 32 := 0x01068123.
Lemma F_92de0 : fetch_word Asan.M.loaded_segments (0x92d84 : word) = Some W_92de0.
Proof. vm_refl. Qed.
Lemma D_92de0 : decode_any W_92de0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92de4 : bv 32 := 0x011681a3.
Lemma F_92de4 : fetch_word Asan.M.loaded_segments (0x92d88 : word) = Some W_92de4.
Proof. vm_refl. Qed.
Lemma D_92de4 : decode_any W_92de4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92de8 : bv 32 := 0x0085c703.
Lemma F_92de8 : fetch_word Asan.M.loaded_segments (0x92d8c : word) = Some W_92de8.
Proof. vm_refl. Qed.
Lemma D_92de8 : decode_any W_92de8 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dec : bv 32 := 0x0095c783.
Lemma F_92dec : fetch_word Asan.M.loaded_segments (0x92d90 : word) = Some W_92dec.
Proof. vm_refl. Qed.
Lemma D_92dec : decode_any W_92dec = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.
Definition W_92df0 : bv 32 := 0x00a5c803.
Lemma F_92df0 : fetch_word Asan.M.loaded_segments (0x92d94 : word) = Some W_92df0.
Proof. vm_refl. Qed.
Lemma D_92df0 : decode_any W_92df0 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_92df4 : bv 32 := 0x00b5c883.
Lemma F_92df4 : fetch_word Asan.M.loaded_segments (0x92d98 : word) = Some W_92df4.
Proof. vm_refl. Qed.
Lemma D_92df4 : decode_any W_92df4 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_92df8 : bv 32 := 0x00568223.
Lemma F_92df8 : fetch_word Asan.M.loaded_segments (0x92d9c : word) = Some W_92df8.
Proof. vm_refl. Qed.
Lemma D_92df8 : decode_any W_92df8 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dfc : bv 32 := 0x006682a3.
Lemma F_92dfc : fetch_word Asan.M.loaded_segments (0x92da0 : word) = Some W_92dfc.
Proof. vm_refl. Qed.
Lemma D_92dfc : decode_any W_92dfc = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e00 : bv 32 := 0x00768323.
Lemma F_92e00 : fetch_word Asan.M.loaded_segments (0x92da4 : word) = Some W_92e00.
Proof. vm_refl. Qed.
Lemma D_92e00 : decode_any W_92e00 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e04 : bv 32 := 0x01c683a3.
Lemma F_92e04 : fetch_word Asan.M.loaded_segments (0x92da8 : word) = Some W_92e04.
Proof. vm_refl. Qed.
Lemma D_92e04 : decode_any W_92e04 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e08 : bv 32 := 0x00c5c283.
Lemma F_92e08 : fetch_word Asan.M.loaded_segments (0x92dac : word) = Some W_92e08.
Proof. vm_refl. Qed.
Lemma D_92e08 : decode_any W_92e08 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e0c : bv 32 := 0x00d5c303.
Lemma F_92e0c : fetch_word Asan.M.loaded_segments (0x92db0 : word) = Some W_92e0c.
Proof. vm_refl. Qed.
Lemma D_92e0c : decode_any W_92e0c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e10 : bv 32 := 0x00e5c383.
Lemma F_92e10 : fetch_word Asan.M.loaded_segments (0x92db4 : word) = Some W_92e10.
Proof. vm_refl. Qed.
Lemma D_92e10 : decode_any W_92e10 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e14 : bv 32 := 0x00f5ce03.
Lemma F_92e14 : fetch_word Asan.M.loaded_segments (0x92db8 : word) = Some W_92e14.
Proof. vm_refl. Qed.
Lemma D_92e14 : decode_any W_92e14 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e18 : bv 32 := 0x01058593.
Lemma F_92e18 : fetch_word Asan.M.loaded_segments (0x92dbc : word) = Some W_92e18.
Proof. vm_refl. Qed.
Lemma D_92e18 : decode_any W_92e18 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e1c : bv 32 := 0x00e68423.
Lemma F_92e1c : fetch_word Asan.M.loaded_segments (0x92dc0 : word) = Some W_92e1c.
Proof. vm_refl. Qed.
Lemma D_92e1c : decode_any W_92e1c = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e20 : bv 32 := 0x00f684a3.
Lemma F_92e20 : fetch_word Asan.M.loaded_segments (0x92dc4 : word) = Some W_92e20.
Proof. vm_refl. Qed.
Lemma D_92e20 : decode_any W_92e20 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e24 : bv 32 := 0x01068523.
Lemma F_92e24 : fetch_word Asan.M.loaded_segments (0x92dc8 : word) = Some W_92e24.
Proof. vm_refl. Qed.
Lemma D_92e24 : decode_any W_92e24 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e28 : bv 32 := 0x011685a3.
Lemma F_92e28 : fetch_word Asan.M.loaded_segments (0x92dcc : word) = Some W_92e28.
Proof. vm_refl. Qed.
Lemma D_92e28 : decode_any W_92e28 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e2c : bv 32 := 0x01068713.
Lemma F_92e2c : fetch_word Asan.M.loaded_segments (0x92dd0 : word) = Some W_92e2c.
Proof. vm_refl. Qed.
Lemma D_92e2c : decode_any W_92e2c = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e30 : bv 32 := 0x00568623.
Lemma F_92e30 : fetch_word Asan.M.loaded_segments (0x92dd4 : word) = Some W_92e30.
Proof. vm_refl. Qed.
Lemma D_92e30 : decode_any W_92e30 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e34 : bv 32 := 0x006686a3.
Lemma F_92e34 : fetch_word Asan.M.loaded_segments (0x92dd8 : word) = Some W_92e34.
Proof. vm_refl. Qed.
Lemma D_92e34 : decode_any W_92e34 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e38 : bv 32 := 0x00768723.
Lemma F_92e38 : fetch_word Asan.M.loaded_segments (0x92ddc : word) = Some W_92e38.
Proof. vm_refl. Qed.
Lemma D_92e38 : decode_any W_92e38 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e3c : bv 32 := 0x01c687a3.
Lemma F_92e3c : fetch_word Asan.M.loaded_segments (0x92de0 : word) = Some W_92e3c.
Proof. vm_refl. Qed.
Lemma D_92e3c : decode_any W_92e3c = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e40 : bv 32 := 0x00070693.
Lemma F_92e40 : fetch_word Asan.M.loaded_segments (0x92de4 : word) = Some W_92e40.
Proof. vm_refl. Qed.
Lemma D_92e40 : decode_any W_92e40 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e44 : bv 32 := 0x00867713.
Lemma F_92e44 : fetch_word Asan.M.loaded_segments (0x92de8 : word) = Some W_92e44.
Proof. vm_refl. Qed.
Lemma D_92e44 : decode_any W_92e44 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e48 : bv 32 := 0xd20706e3.
Lemma F_92e48 : fetch_word Asan.M.loaded_segments (0x92dec : word) = Some W_92e48.
Proof. vm_refl. Qed.
Lemma D_92e48 : decode_any W_92e48 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e4c : bv 32 := 0x0005c703.
Lemma F_92e4c : fetch_word Asan.M.loaded_segments (0x92df0 : word) = Some W_92e4c.
Proof. vm_refl. Qed.
Lemma D_92e4c : decode_any W_92e4c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e50 : bv 32 := 0x0015c783.
Lemma F_92e50 : fetch_word Asan.M.loaded_segments (0x92df4 : word) = Some W_92e50.
Proof. vm_refl. Qed.
Lemma D_92e50 : decode_any W_92e50 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e54 : bv 32 := 0x0025c803.
Lemma F_92e54 : fetch_word Asan.M.loaded_segments (0x92df8 : word) = Some W_92e54.
Proof. vm_refl. Qed.
Lemma D_92e54 : decode_any W_92e54 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e58 : bv 32 := 0x0035c883.
Lemma F_92e58 : fetch_word Asan.M.loaded_segments (0x92dfc : word) = Some W_92e58.
Proof. vm_refl. Qed.
Lemma D_92e58 : decode_any W_92e58 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e5c : bv 32 := 0x0045c283.
Lemma F_92e5c : fetch_word Asan.M.loaded_segments (0x92e00 : word) = Some W_92e5c.
Proof. vm_refl. Qed.
Lemma D_92e5c : decode_any W_92e5c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e60 : bv 32 := 0x0055c303.
Lemma F_92e60 : fetch_word Asan.M.loaded_segments (0x92e04 : word) = Some W_92e60.
Proof. vm_refl. Qed.
Lemma D_92e60 : decode_any W_92e60 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e64 : bv 32 := 0x0065c383.
Lemma F_92e64 : fetch_word Asan.M.loaded_segments (0x92e08 : word) = Some W_92e64.
Proof. vm_refl. Qed.
Lemma D_92e64 : decode_any W_92e64 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e68 : bv 32 := 0x0075ce03.
Lemma F_92e68 : fetch_word Asan.M.loaded_segments (0x92e0c : word) = Some W_92e68.
Proof. vm_refl. Qed.
Lemma D_92e68 : decode_any W_92e68 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e6c : bv 32 := 0x00858593.
Lemma F_92e6c : fetch_word Asan.M.loaded_segments (0x92e10 : word) = Some W_92e6c.
Proof. vm_refl. Qed.
Lemma D_92e6c : decode_any W_92e6c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e70 : bv 32 := 0x00e68023.
Lemma F_92e70 : fetch_word Asan.M.loaded_segments (0x92e14 : word) = Some W_92e70.
Proof. vm_refl. Qed.
Lemma D_92e70 : decode_any W_92e70 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e74 : bv 32 := 0x00f680a3.
Lemma F_92e74 : fetch_word Asan.M.loaded_segments (0x92e18 : word) = Some W_92e74.
Proof. vm_refl. Qed.
Lemma D_92e74 : decode_any W_92e74 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e78 : bv 32 := 0x01068123.
Lemma F_92e78 : fetch_word Asan.M.loaded_segments (0x92e1c : word) = Some W_92e78.
Proof. vm_refl. Qed.
Lemma D_92e78 : decode_any W_92e78 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e7c : bv 32 := 0x011681a3.
Lemma F_92e7c : fetch_word Asan.M.loaded_segments (0x92e20 : word) = Some W_92e7c.
Proof. vm_refl. Qed.
Lemma D_92e7c : decode_any W_92e7c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e80 : bv 32 := 0x00868713.
Lemma F_92e80 : fetch_word Asan.M.loaded_segments (0x92e24 : word) = Some W_92e80.
Proof. vm_refl. Qed.
Lemma D_92e80 : decode_any W_92e80 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e84 : bv 32 := 0x00568223.
Lemma F_92e84 : fetch_word Asan.M.loaded_segments (0x92e28 : word) = Some W_92e84.
Proof. vm_refl. Qed.
Lemma D_92e84 : decode_any W_92e84 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e88 : bv 32 := 0x006682a3.
Lemma F_92e88 : fetch_word Asan.M.loaded_segments (0x92e2c : word) = Some W_92e88.
Proof. vm_refl. Qed.
Lemma D_92e88 : decode_any W_92e88 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e8c : bv 32 := 0x00768323.
Lemma F_92e8c : fetch_word Asan.M.loaded_segments (0x92e30 : word) = Some W_92e8c.
Proof. vm_refl. Qed.
Lemma D_92e8c : decode_any W_92e8c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e90 : bv 32 := 0x01c683a3.
Lemma F_92e90 : fetch_word Asan.M.loaded_segments (0x92e34 : word) = Some W_92e90.
Proof. vm_refl. Qed.
Lemma D_92e90 : decode_any W_92e90 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e94 : bv 32 := 0x00070693.
Lemma F_92e94 : fetch_word Asan.M.loaded_segments (0x92e38 : word) = Some W_92e94.
Proof. vm_refl. Qed.
Lemma D_92e94 : decode_any W_92e94 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e98 : bv 32 := 0x00467713.
Lemma F_92e98 : fetch_word Asan.M.loaded_segments (0x92e3c : word) = Some W_92e98.
Proof. vm_refl. Qed.
Lemma D_92e98 : decode_any W_92e98 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e9c : bv 32 := 0x02070863.
Lemma F_92e9c : fetch_word Asan.M.loaded_segments (0x92e40 : word) = Some W_92e9c.
Proof. vm_refl. Qed.
Lemma D_92e9c : decode_any W_92e9c = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ea0 : bv 32 := 0x0005c703.
Lemma F_92ea0 : fetch_word Asan.M.loaded_segments (0x92e44 : word) = Some W_92ea0.
Proof. vm_refl. Qed.
Lemma D_92ea0 : decode_any W_92ea0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ea4 : bv 32 := 0x0015c783.
Lemma F_92ea4 : fetch_word Asan.M.loaded_segments (0x92e48 : word) = Some W_92ea4.
Proof. vm_refl. Qed.
Lemma D_92ea4 : decode_any W_92ea4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ea8 : bv 32 := 0x0025c803.
Lemma F_92ea8 : fetch_word Asan.M.loaded_segments (0x92e4c : word) = Some W_92ea8.
Proof. vm_refl. Qed.
Lemma D_92ea8 : decode_any W_92ea8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92eac : bv 32 := 0x0035c883.
Lemma F_92eac : fetch_word Asan.M.loaded_segments (0x92e50 : word) = Some W_92eac.
Proof. vm_refl. Qed.
Lemma D_92eac : decode_any W_92eac = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92eb0 : bv 32 := 0x00458593.
Lemma F_92eb0 : fetch_word Asan.M.loaded_segments (0x92e54 : word) = Some W_92eb0.
Proof. vm_refl. Qed.
Lemma D_92eb0 : decode_any W_92eb0 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92eb4 : bv 32 := 0x00468293.
Lemma F_92eb4 : fetch_word Asan.M.loaded_segments (0x92e58 : word) = Some W_92eb4.
Proof. vm_refl. Qed.
Lemma D_92eb4 : decode_any W_92eb4 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92eb8 : bv 32 := 0x00e68023.
Lemma F_92eb8 : fetch_word Asan.M.loaded_segments (0x92e5c : word) = Some W_92eb8.
Proof. vm_refl. Qed.
Lemma D_92eb8 : decode_any W_92eb8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ebc : bv 32 := 0x00f680a3.
Lemma F_92ebc : fetch_word Asan.M.loaded_segments (0x92e60 : word) = Some W_92ebc.
Proof. vm_refl. Qed.
Lemma D_92ebc : decode_any W_92ebc = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ec0 : bv 32 := 0x01068123.
Lemma F_92ec0 : fetch_word Asan.M.loaded_segments (0x92e64 : word) = Some W_92ec0.
Proof. vm_refl. Qed.
Lemma D_92ec0 : decode_any W_92ec0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ec4 : bv 32 := 0x011681a3.
Lemma F_92ec4 : fetch_word Asan.M.loaded_segments (0x92e68 : word) = Some W_92ec4.
Proof. vm_refl. Qed.
Lemma D_92ec4 : decode_any W_92ec4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ec8 : bv 32 := 0x00028693.
Lemma F_92ec8 : fetch_word Asan.M.loaded_segments (0x92e6c : word) = Some W_92ec8.
Proof. vm_refl. Qed.
Lemma D_92ec8 : decode_any W_92ec8 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ecc : bv 32 := 0x00267713.
Lemma F_92ecc : fetch_word Asan.M.loaded_segments (0x92e70 : word) = Some W_92ecc.
Proof. vm_refl. Qed.
Lemma D_92ecc : decode_any W_92ecc = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ed0 : bv 32 := 0x00071863.
Lemma F_92ed0 : fetch_word Asan.M.loaded_segments (0x92e74 : word) = Some W_92ed0.
Proof. vm_refl. Qed.
Lemma D_92ed0 : decode_any W_92ed0 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ed4 : bv 32 := 0x00167613.
Lemma F_92ed4 : fetch_word Asan.M.loaded_segments (0x92e78 : word) = Some W_92ed4.
Proof. vm_refl. Qed.
Lemma D_92ed4 : decode_any W_92ed4 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ed8 : bv 32 := 0x02061663.
Lemma F_92ed8 : fetch_word Asan.M.loaded_segments (0x92e7c : word) = Some W_92ed8.
Proof. vm_refl. Qed.
Lemma D_92ed8 : decode_any W_92ed8 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.
Definition W_92edc : bv 32 := 0x00008067.
Lemma F_92edc : fetch_word Asan.M.loaded_segments (0x92e80 : word) = Some W_92edc.
Proof. vm_refl. Qed.
Lemma D_92edc : decode_any W_92edc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ee0 : bv 32 := 0x0005c703.
Lemma F_92ee0 : fetch_word Asan.M.loaded_segments (0x92e84 : word) = Some W_92ee0.
Proof. vm_refl. Qed.
Lemma D_92ee0 : decode_any W_92ee0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ee4 : bv 32 := 0x0015c783.
Lemma F_92ee4 : fetch_word Asan.M.loaded_segments (0x92e88 : word) = Some W_92ee4.
Proof. vm_refl. Qed.
Lemma D_92ee4 : decode_any W_92ee4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ee8 : bv 32 := 0x00258593.
Lemma F_92ee8 : fetch_word Asan.M.loaded_segments (0x92e8c : word) = Some W_92ee8.
Proof. vm_refl. Qed.
Lemma D_92ee8 : decode_any W_92ee8 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92eec : bv 32 := 0x00268813.
Lemma F_92eec : fetch_word Asan.M.loaded_segments (0x92e90 : word) = Some W_92eec.
Proof. vm_refl. Qed.
Lemma D_92eec : decode_any W_92eec = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ef0 : bv 32 := 0x00e68023.
Lemma F_92ef0 : fetch_word Asan.M.loaded_segments (0x92e94 : word) = Some W_92ef0.
Proof. vm_refl. Qed.
Lemma D_92ef0 : decode_any W_92ef0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ef4 : bv 32 := 0x00f680a3.
Lemma F_92ef4 : fetch_word Asan.M.loaded_segments (0x92e98 : word) = Some W_92ef4.
Proof. vm_refl. Qed.
Lemma D_92ef4 : decode_any W_92ef4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ef8 : bv 32 := 0x00080693.
Lemma F_92ef8 : fetch_word Asan.M.loaded_segments (0x92e9c : word) = Some W_92ef8.
Proof. vm_refl. Qed.
Lemma D_92ef8 : decode_any W_92ef8 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92efc : bv 32 := 0x00167613.
Lemma F_92efc : fetch_word Asan.M.loaded_segments (0x92ea0 : word) = Some W_92efc.
Proof. vm_refl. Qed.
Lemma D_92efc : decode_any W_92efc = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f00 : bv 32 := 0xfc060ee3.
Lemma F_92f00 : fetch_word Asan.M.loaded_segments (0x92ea4 : word) = Some W_92f00.
Proof. vm_refl. Qed.
Lemma D_92f00 : decode_any W_92f00 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f04 : bv 32 := 0x0005c583.
Lemma F_92f04 : fetch_word Asan.M.loaded_segments (0x92ea8 : word) = Some W_92f04.
Proof. vm_refl. Qed.
Lemma D_92f04 : decode_any W_92f04 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f08 : bv 32 := 0x00b68023.
Lemma F_92f08 : fetch_word Asan.M.loaded_segments (0x92eac : word) = Some W_92f08.
Proof. vm_refl. Qed.
Lemma D_92f08 : decode_any W_92f08 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f0c : bv 32 := 0x00008067.
Lemma F_92f0c : fetch_word Asan.M.loaded_segments (0x92eb0 : word) = Some W_92f0c.
Proof. vm_refl. Qed.
Lemma D_92f0c : decode_any W_92f0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
