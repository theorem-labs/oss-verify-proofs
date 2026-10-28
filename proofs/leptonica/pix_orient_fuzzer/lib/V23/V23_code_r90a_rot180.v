(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_98a70 : bv 32 := 0xfe010113.
Lemma F_98a70 : fetch_word Ubsan.M.loaded_segments (0x98a70 : word) = Some W_98a70.
Proof. vm_refl. Qed.
Lemma D_98a70 : decode_any W_98a70 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a74 : bv 32 := 0x00113c23.
Lemma F_98a74 : fetch_word Ubsan.M.loaded_segments (0x98a74 : word) = Some W_98a74.
Proof. vm_refl. Qed.
Lemma D_98a74 : decode_any W_98a74 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a78 : bv 32 := 0x00813823.
Lemma F_98a78 : fetch_word Ubsan.M.loaded_segments (0x98a78 : word) = Some W_98a78.
Proof. vm_refl. Qed.
Lemma D_98a78 : decode_any W_98a78 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a7c : bv 32 := 0x00913423.
Lemma F_98a7c : fetch_word Ubsan.M.loaded_segments (0x98a7c : word) = Some W_98a7c.
Proof. vm_refl. Qed.
Lemma D_98a7c : decode_any W_98a7c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a80 : bv 32 := 0x06058063.
Lemma F_98a80 : fetch_word Ubsan.M.loaded_segments (0x98a80 : word) = Some W_98a80.
Proof. vm_refl. Qed.
Lemma D_98a80 : decode_any W_98a80 = Some (Branch BC_EQ 11 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a84 : bv 32 := 0x00058413.
Lemma F_98a84 : fetch_word Ubsan.M.loaded_segments (0x98a84 : word) = Some W_98a84.
Proof. vm_refl. Qed.
Lemma D_98a84 : decode_any W_98a84 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a88 : bv 32 := 0x00050493.
Lemma F_98a88 : fetch_word Ubsan.M.loaded_segments (0x98a88 : word) = Some W_98a88.
Proof. vm_refl. Qed.
Lemma D_98a88 : decode_any W_98a88 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a8c : bv 32 := 0x00058513.
Lemma F_98a8c : fetch_word Ubsan.M.loaded_segments (0x98a8c : word) = Some W_98a8c.
Proof. vm_refl. Qed.
Lemma D_98a8c : decode_any W_98a8c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a90 : bv 32 := 0xe84d60ef.
Lemma F_98a90 : fetch_word Ubsan.M.loaded_segments (0x98a90 : word) = Some W_98a90.
Proof. vm_refl. Qed.
Lemma D_98a90 : decode_any W_98a90 = Some (Jal 1 1926788, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a94 : bv 32 := 0x02000593.
Lemma F_98a94 : fetch_word Ubsan.M.loaded_segments (0x98a94 : word) = Some W_98a94.
Proof. vm_refl. Qed.
Lemma D_98a94 : decode_any W_98a94 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a98 : bv 32 := 0x08a5ec63.
Lemma F_98a98 : fetch_word Ubsan.M.loaded_segments (0x98a98 : word) = Some W_98a98.
Proof. vm_refl. Qed.
Lemma D_98a98 : decode_any W_98a98 = Some (Branch BC_LTU 11 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a9c : bv 32 := 0x100015b7.
Lemma F_98a9c : fetch_word Ubsan.M.loaded_segments (0x98a9c : word) = Some W_98a9c.
Proof. vm_refl. Qed.
Lemma D_98a9c : decode_any W_98a9c = Some (Lui 11 65537, 4%Z).
Proof. vm_refl. Qed.

Definition W_98aa0 : bv 32 := 0x00459593.
Lemma F_98aa0 : fetch_word Ubsan.M.loaded_segments (0x98aa0 : word) = Some W_98aa0.
Proof. vm_refl. Qed.
Lemma D_98aa0 : decode_any W_98aa0 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_98aa4 : bv 32 := 0x11658593.
Lemma F_98aa4 : fetch_word Ubsan.M.loaded_segments (0x98aa4 : word) = Some W_98aa4.
Proof. vm_refl. Qed.
Lemma D_98aa4 : decode_any W_98aa4 = Some (OpImm ALU_ADD 11 11 278, 4%Z).
Proof. vm_refl. Qed.

Definition W_98aa8 : bv 32 := 0x00a5d533.
Lemma F_98aa8 : fetch_word Ubsan.M.loaded_segments (0x98aa8 : word) = Some W_98aa8.
Proof. vm_refl. Qed.
Lemma D_98aa8 : decode_any W_98aa8 = Some (Op ALU_SRL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_98aac : bv 32 := 0x00157513.
Lemma F_98aac : fetch_word Ubsan.M.loaded_segments (0x98aac : word) = Some W_98aac.
Proof. vm_refl. Qed.
Lemma D_98aac : decode_any W_98aac = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ab0 : bv 32 := 0x08050063.
Lemma F_98ab0 : fetch_word Ubsan.M.loaded_segments (0x98ab0 : word) = Some W_98ab0.
Proof. vm_refl. Qed.
Lemma D_98ab0 : decode_any W_98ab0 = Some (Branch BC_EQ 10 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ab4 : bv 32 := 0x00048513.
Lemma F_98ab4 : fetch_word Ubsan.M.loaded_segments (0x98ab4 : word) = Some W_98ab4.
Proof. vm_refl. Qed.
Lemma D_98ab4 : decode_any W_98ab4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ab8 : bv 32 := 0x00040593.
Lemma F_98ab8 : fetch_word Ubsan.M.loaded_segments (0x98ab8 : word) = Some W_98ab8.
Proof. vm_refl. Qed.
Lemma D_98ab8 : decode_any W_98ab8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98abc : bv 32 := 0x8a0d60ef.
Lemma F_98abc : fetch_word Ubsan.M.loaded_segments (0x98abc : word) = Some W_98abc.
Proof. vm_refl. Qed.
Lemma D_98abc : decode_any W_98abc = Some (Jal 1 1925280, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ac0 : bv 32 := 0x04050463.
Lemma F_98ac0 : fetch_word Ubsan.M.loaded_segments (0x98ac0 : word) = Some W_98ac0.
Proof. vm_refl. Qed.
Lemma D_98ac0 : decode_any W_98ac0 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ac4 : bv 32 := 0x00050413.
Lemma F_98ac4 : fetch_word Ubsan.M.loaded_segments (0x98ac4 : word) = Some W_98ac4.
Proof. vm_refl. Qed.
Lemma D_98ac4 : decode_any W_98ac4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ac8 : bv 32 := 0x00050593.
Lemma F_98ac8 : fetch_word Ubsan.M.loaded_segments (0x98ac8 : word) = Some W_98ac8.
Proof. vm_refl. Qed.
Lemma D_98ac8 : decode_any W_98ac8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98acc : bv 32 := 0x0bc000ef.
Lemma F_98acc : fetch_word Ubsan.M.loaded_segments (0x98acc : word) = Some W_98acc.
Proof. vm_refl. Qed.
Lemma D_98acc : decode_any W_98acc = Some (Jal 1 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ad0 : bv 32 := 0x00040513.
Lemma F_98ad0 : fetch_word Ubsan.M.loaded_segments (0x98ad0 : word) = Some W_98ad0.
Proof. vm_refl. Qed.
Lemma D_98ad0 : decode_any W_98ad0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ad4 : bv 32 := 0x00040593.
Lemma F_98ad4 : fetch_word Ubsan.M.loaded_segments (0x98ad4 : word) = Some W_98ad4.
Proof. vm_refl. Qed.
Lemma D_98ad4 : decode_any W_98ad4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ad8 : bv 32 := 0x509000ef.
Lemma F_98ad8 : fetch_word Ubsan.M.loaded_segments (0x98ad8 : word) = Some W_98ad8.
Proof. vm_refl. Qed.
Lemma D_98ad8 : decode_any W_98ad8 = Some (Jal 1 3336, 4%Z).
Proof. vm_refl. Qed.

Definition W_98adc : bv 32 := 0x0940006f.
Lemma F_98adc : fetch_word Ubsan.M.loaded_segments (0x98adc : word) = Some W_98adc.
Proof. vm_refl. Qed.
Lemma D_98adc : decode_any W_98adc = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ae0 : bv 32 := 0x0008e517.
Lemma F_98ae0 : fetch_word Ubsan.M.loaded_segments (0x98ae0 : word) = Some W_98ae0.
Proof. vm_refl. Qed.
Lemma D_98ae0 : decode_any W_98ae0 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ae4 : bv 32 := 0xf9053503.
Lemma F_98ae4 : fetch_word Ubsan.M.loaded_segments (0x98ae4 : word) = Some W_98ae4.
Proof. vm_refl. Qed.
Lemma D_98ae4 : decode_any W_98ae4 = Some (Load SZ8 true 10 10 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ae8 : bv 32 := 0x00052503.
Lemma F_98ae8 : fetch_word Ubsan.M.loaded_segments (0x98ae8 : word) = Some W_98ae8.
Proof. vm_refl. Qed.
Lemma D_98ae8 : decode_any W_98ae8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98aec : bv 32 := 0x00500593.
Lemma F_98aec : fetch_word Ubsan.M.loaded_segments (0x98aec : word) = Some W_98aec.
Proof. vm_refl. Qed.
Lemma D_98aec : decode_any W_98aec = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_98af0 : bv 32 := 0x06a5ce63.
Lemma F_98af0 : fetch_word Ubsan.M.loaded_segments (0x98af0 : word) = Some W_98af0.
Proof. vm_refl. Qed.
Lemma D_98af0 : decode_any W_98af0 = Some (Branch BC_LT 11 10 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_98af4 : bv 32 := 0xfff78517.
Lemma F_98af4 : fetch_word Ubsan.M.loaded_segments (0x98af4 : word) = Some W_98af4.
Proof. vm_refl. Qed.
Lemma D_98af4 : decode_any W_98af4 = Some (Auipc 10 1048440, 4%Z).
Proof. vm_refl. Qed.

Definition W_98af8 : bv 32 := 0xfff7b597.
Lemma F_98af8 : fetch_word Ubsan.M.loaded_segments (0x98af8 : word) = Some W_98af8.
Proof. vm_refl. Qed.
Lemma D_98af8 : decode_any W_98af8 = Some (Auipc 11 1048443, 4%Z).
Proof. vm_refl. Qed.

Definition W_98afc : bv 32 := 0x86150513.
Lemma F_98afc : fetch_word Ubsan.M.loaded_segments (0x98afc : word) = Some W_98afc.
Proof. vm_refl. Qed.
Lemma D_98afc : decode_any W_98afc = Some (OpImm ALU_ADD 10 10 2145, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b00 : bv 32 := 0x31058593.
Lemma F_98b00 : fetch_word Ubsan.M.loaded_segments (0x98b00 : word) = Some W_98b00.
Proof. vm_refl. Qed.
Lemma D_98b00 : decode_any W_98b00 = Some (OpImm ALU_ADD 11 11 784, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b04 : bv 32 := 0x0500006f.
Lemma F_98b04 : fetch_word Ubsan.M.loaded_segments (0x98b04 : word) = Some W_98b04.
Proof. vm_refl. Qed.
Lemma D_98b04 : decode_any W_98b04 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b08 : bv 32 := 0x0008e517.
Lemma F_98b08 : fetch_word Ubsan.M.loaded_segments (0x98b08 : word) = Some W_98b08.
Proof. vm_refl. Qed.
Lemma D_98b08 : decode_any W_98b08 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b0c : bv 32 := 0xf6853503.
Lemma F_98b0c : fetch_word Ubsan.M.loaded_segments (0x98b0c : word) = Some W_98b0c.
Proof. vm_refl. Qed.
Lemma D_98b0c : decode_any W_98b0c = Some (Load SZ8 true 10 10 3944, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b10 : bv 32 := 0x00052503.
Lemma F_98b10 : fetch_word Ubsan.M.loaded_segments (0x98b10 : word) = Some W_98b10.
Proof. vm_refl. Qed.
Lemma D_98b10 : decode_any W_98b10 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b14 : bv 32 := 0x00500593.
Lemma F_98b14 : fetch_word Ubsan.M.loaded_segments (0x98b14 : word) = Some W_98b14.
Proof. vm_refl. Qed.
Lemma D_98b14 : decode_any W_98b14 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b18 : bv 32 := 0x04a5ca63.
Lemma F_98b18 : fetch_word Ubsan.M.loaded_segments (0x98b18 : word) = Some W_98b18.
Proof. vm_refl. Qed.
Lemma D_98b18 : decode_any W_98b18 = Some (Branch BC_LT 11 10 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b1c : bv 32 := 0xfff7a517.
Lemma F_98b1c : fetch_word Ubsan.M.loaded_segments (0x98b1c : word) = Some W_98b1c.
Proof. vm_refl. Qed.
Lemma D_98b1c : decode_any W_98b1c = Some (Auipc 10 1048442, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b20 : bv 32 := 0xfff7b597.
Lemma F_98b20 : fetch_word Ubsan.M.loaded_segments (0x98b20 : word) = Some W_98b20.
Proof. vm_refl. Qed.
Lemma D_98b20 : decode_any W_98b20 = Some (Auipc 11 1048443, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b24 : bv 32 := 0xbbe50513.
Lemma F_98b24 : fetch_word Ubsan.M.loaded_segments (0x98b24 : word) = Some W_98b24.
Proof. vm_refl. Qed.
Lemma D_98b24 : decode_any W_98b24 = Some (OpImm ALU_ADD 10 10 3006, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b28 : bv 32 := 0x2e858593.
Lemma F_98b28 : fetch_word Ubsan.M.loaded_segments (0x98b28 : word) = Some W_98b28.
Proof. vm_refl. Qed.
Lemma D_98b28 : decode_any W_98b28 = Some (OpImm ALU_ADD 11 11 744, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b2c : bv 32 := 0x0280006f.
Lemma F_98b2c : fetch_word Ubsan.M.loaded_segments (0x98b2c : word) = Some W_98b2c.
Proof. vm_refl. Qed.
Lemma D_98b2c : decode_any W_98b2c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b30 : bv 32 := 0x0008e517.
Lemma F_98b30 : fetch_word Ubsan.M.loaded_segments (0x98b30 : word) = Some W_98b30.
Proof. vm_refl. Qed.
Lemma D_98b30 : decode_any W_98b30 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b34 : bv 32 := 0xf4053503.
Lemma F_98b34 : fetch_word Ubsan.M.loaded_segments (0x98b34 : word) = Some W_98b34.
Proof. vm_refl. Qed.
Lemma D_98b34 : decode_any W_98b34 = Some (Load SZ8 true 10 10 3904, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b38 : bv 32 := 0x00052503.
Lemma F_98b38 : fetch_word Ubsan.M.loaded_segments (0x98b38 : word) = Some W_98b38.
Proof. vm_refl. Qed.
Lemma D_98b38 : decode_any W_98b38 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b3c : bv 32 := 0x00500593.
Lemma F_98b3c : fetch_word Ubsan.M.loaded_segments (0x98b3c : word) = Some W_98b3c.
Proof. vm_refl. Qed.
Lemma D_98b3c : decode_any W_98b3c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b40 : bv 32 := 0x02a5c663.
Lemma F_98b40 : fetch_word Ubsan.M.loaded_segments (0x98b40 : word) = Some W_98b40.
Proof. vm_refl. Qed.
Lemma D_98b40 : decode_any W_98b40 = Some (Branch BC_LT 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b44 : bv 32 := 0xfff7b517.
Lemma F_98b44 : fetch_word Ubsan.M.loaded_segments (0x98b44 : word) = Some W_98b44.
Proof. vm_refl. Qed.
Lemma D_98b44 : decode_any W_98b44 = Some (Auipc 10 1048443, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b48 : bv 32 := 0xfff7b597.
Lemma F_98b48 : fetch_word Ubsan.M.loaded_segments (0x98b48 : word) = Some W_98b48.
Proof. vm_refl. Qed.
Lemma D_98b48 : decode_any W_98b48 = Some (Auipc 11 1048443, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b4c : bv 32 := 0xab150513.
Lemma F_98b4c : fetch_word Ubsan.M.loaded_segments (0x98b4c : word) = Some W_98b4c.
Proof. vm_refl. Qed.
Lemma D_98b4c : decode_any W_98b4c = Some (OpImm ALU_ADD 10 10 2737, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b50 : bv 32 := 0x2c058593.
Lemma F_98b50 : fetch_word Ubsan.M.loaded_segments (0x98b50 : word) = Some W_98b50.
Proof. vm_refl. Qed.
Lemma D_98b50 : decode_any W_98b50 = Some (OpImm ALU_ADD 11 11 704, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b54 : bv 32 := 0x00000613.
Lemma F_98b54 : fetch_word Ubsan.M.loaded_segments (0x98b54 : word) = Some W_98b54.
Proof. vm_refl. Qed.
Lemma D_98b54 : decode_any W_98b54 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b58 : bv 32 := 0x01813083.
Lemma F_98b58 : fetch_word Ubsan.M.loaded_segments (0x98b58 : word) = Some W_98b58.
Proof. vm_refl. Qed.
Lemma D_98b58 : decode_any W_98b58 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b5c : bv 32 := 0x01013403.
Lemma F_98b5c : fetch_word Ubsan.M.loaded_segments (0x98b5c : word) = Some W_98b5c.
Proof. vm_refl. Qed.
Lemma D_98b5c : decode_any W_98b5c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b60 : bv 32 := 0x00813483.
Lemma F_98b60 : fetch_word Ubsan.M.loaded_segments (0x98b60 : word) = Some W_98b60.
Proof. vm_refl. Qed.
Lemma D_98b60 : decode_any W_98b60 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b64 : bv 32 := 0x02010113.
Lemma F_98b64 : fetch_word Ubsan.M.loaded_segments (0x98b64 : word) = Some W_98b64.
Proof. vm_refl. Qed.
Lemma D_98b64 : decode_any W_98b64 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b68 : bv 32 := 0xbd9ca06f.
Lemma F_98b68 : fetch_word Ubsan.M.loaded_segments (0x98b68 : word) = Some W_98b68.
Proof. vm_refl. Qed.
Lemma D_98b68 : decode_any W_98b68 = Some (Jal 0 1879000, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b6c : bv 32 := 0x00000413.
Lemma F_98b6c : fetch_word Ubsan.M.loaded_segments (0x98b6c : word) = Some W_98b6c.
Proof. vm_refl. Qed.
Lemma D_98b6c : decode_any W_98b6c = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b70 : bv 32 := 0x00040513.
Lemma F_98b70 : fetch_word Ubsan.M.loaded_segments (0x98b70 : word) = Some W_98b70.
Proof. vm_refl. Qed.
Lemma D_98b70 : decode_any W_98b70 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b74 : bv 32 := 0x01813083.
Lemma F_98b74 : fetch_word Ubsan.M.loaded_segments (0x98b74 : word) = Some W_98b74.
Proof. vm_refl. Qed.
Lemma D_98b74 : decode_any W_98b74 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b78 : bv 32 := 0x01013403.
Lemma F_98b78 : fetch_word Ubsan.M.loaded_segments (0x98b78 : word) = Some W_98b78.
Proof. vm_refl. Qed.
Lemma D_98b78 : decode_any W_98b78 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b7c : bv 32 := 0x00813483.
Lemma F_98b7c : fetch_word Ubsan.M.loaded_segments (0x98b7c : word) = Some W_98b7c.
Proof. vm_refl. Qed.
Lemma D_98b7c : decode_any W_98b7c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b80 : bv 32 := 0x02010113.
Lemma F_98b80 : fetch_word Ubsan.M.loaded_segments (0x98b80 : word) = Some W_98b80.
Proof. vm_refl. Qed.
Lemma D_98b80 : decode_any W_98b80 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b84 : bv 32 := 0x00008067.
Lemma F_98b84 : fetch_word Ubsan.M.loaded_segments (0x98b84 : word) = Some W_98b84.
Proof. vm_refl. Qed.
Lemma D_98b84 : decode_any W_98b84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
