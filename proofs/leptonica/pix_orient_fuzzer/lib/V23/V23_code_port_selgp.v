(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushU23.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a4fd0 : bv 32 := 0x0035f793.
Lemma F_a4fd0 : fetch_word Ubsan.M.loaded_segments (0xa4fd0 : word) = Some W_a4fd0.
Proof. vm_refl. Qed.
Lemma D_a4fd0 : decode_any W_a4fd0 = Some (OpImm ALU_AND 15 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4fd4 : bv 32 := 0x00058663.
Lemma F_a4fd4 : fetch_word Ubsan.M.loaded_segments (0xa4fd4 : word) = Some W_a4fd4.
Proof. vm_refl. Qed.
Lemma D_a4fd4 : decode_any W_a4fd4 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4fd8 : bv 32 := 0x0c079a63.
Lemma F_a4fd8 : fetch_word Ubsan.M.loaded_segments (0xa4fd8 : word) = Some W_a4fd8.
Proof. vm_refl. Qed.
Lemma D_a4fd8 : decode_any W_a4fd8 = Some (Branch BC_NE 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4fdc : bv 32 := 0x0005a023.
Lemma F_a4fdc : fetch_word Ubsan.M.loaded_segments (0xa4fdc : word) = Some W_a4fdc.
Proof. vm_refl. Qed.
Lemma D_a4fdc : decode_any W_a4fdc = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4fe0 : bv 32 := 0x00367813.
Lemma F_a4fe0 : fetch_word Ubsan.M.loaded_segments (0xa4fe0 : word) = Some W_a4fe0.
Proof. vm_refl. Qed.
Lemma D_a4fe0 : decode_any W_a4fe0 = Some (OpImm ALU_AND 16 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4fe4 : bv 32 := 0x00060663.
Lemma F_a4fe4 : fetch_word Ubsan.M.loaded_segments (0xa4fe4 : word) = Some W_a4fe4.
Proof. vm_refl. Qed.
Lemma D_a4fe4 : decode_any W_a4fe4 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4fe8 : bv 32 := 0x0c081263.
Lemma F_a4fe8 : fetch_word Ubsan.M.loaded_segments (0xa4fe8 : word) = Some W_a4fe8.
Proof. vm_refl. Qed.
Lemma D_a4fe8 : decode_any W_a4fe8 = Some (Branch BC_NE 16 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4fec : bv 32 := 0x00062023.
Lemma F_a4fec : fetch_word Ubsan.M.loaded_segments (0xa4fec : word) = Some W_a4fec.
Proof. vm_refl. Qed.
Lemma D_a4fec : decode_any W_a4fec = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ff0 : bv 32 := 0x0036f893.
Lemma F_a4ff0 : fetch_word Ubsan.M.loaded_segments (0xa4ff0 : word) = Some W_a4ff0.
Proof. vm_refl. Qed.
Lemma D_a4ff0 : decode_any W_a4ff0 = Some (OpImm ALU_AND 17 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ff4 : bv 32 := 0x00068663.
Lemma F_a4ff4 : fetch_word Ubsan.M.loaded_segments (0xa4ff4 : word) = Some W_a4ff4.
Proof. vm_refl. Qed.
Lemma D_a4ff4 : decode_any W_a4ff4 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ff8 : bv 32 := 0x0a089a63.
Lemma F_a4ff8 : fetch_word Ubsan.M.loaded_segments (0xa4ff8 : word) = Some W_a4ff8.
Proof. vm_refl. Qed.
Lemma D_a4ff8 : decode_any W_a4ff8 = Some (Branch BC_NE 17 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a4ffc : bv 32 := 0x0006a023.
Lemma F_a4ffc : fetch_word Ubsan.M.loaded_segments (0xa4ffc : word) = Some W_a4ffc.
Proof. vm_refl. Qed.
Lemma D_a4ffc : decode_any W_a4ffc = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5000 : bv 32 := 0x00377293.
Lemma F_a5000 : fetch_word Ubsan.M.loaded_segments (0xa5000 : word) = Some W_a5000.
Proof. vm_refl. Qed.
Lemma D_a5000 : decode_any W_a5000 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5004 : bv 32 := 0x00070663.
Lemma F_a5004 : fetch_word Ubsan.M.loaded_segments (0xa5004 : word) = Some W_a5004.
Proof. vm_refl. Qed.
Lemma D_a5004 : decode_any W_a5004 = Some (Branch BC_EQ 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5008 : bv 32 := 0x0a029263.
Lemma F_a5008 : fetch_word Ubsan.M.loaded_segments (0xa5008 : word) = Some W_a5008.
Proof. vm_refl. Qed.
Lemma D_a5008 : decode_any W_a5008 = Some (Branch BC_NE 5 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_a500c : bv 32 := 0x00072023.
Lemma F_a500c : fetch_word Ubsan.M.loaded_segments (0xa500c : word) = Some W_a500c.
Proof. vm_refl. Qed.
Lemma D_a500c : decode_any W_a500c = Some (Store SZ4 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5010 : bv 32 := 0x06050063.
Lemma F_a5010 : fetch_word Ubsan.M.loaded_segments (0xa5010 : word) = Some W_a5010.
Proof. vm_refl. Qed.
Lemma D_a5010 : decode_any W_a5010 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5014 : bv 32 := 0x00757313.
Lemma F_a5014 : fetch_word Ubsan.M.loaded_segments (0xa5014 : word) = Some W_a5014.
Proof. vm_refl. Qed.
Lemma D_a5014 : decode_any W_a5014 = Some (OpImm ALU_AND 6 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5018 : bv 32 := 0x00058a63.
Lemma F_a5018 : fetch_word Ubsan.M.loaded_segments (0xa5018 : word) = Some W_a5018.
Proof. vm_refl. Qed.
Lemma D_a5018 : decode_any W_a5018 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a501c : bv 32 := 0x00f367b3.
Lemma F_a501c : fetch_word Ubsan.M.loaded_segments (0xa501c : word) = Some W_a501c.
Proof. vm_refl. Qed.
Lemma D_a501c : decode_any W_a501c = Some (Op ALU_OR 15 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5020 : bv 32 := 0x08079663.
Lemma F_a5020 : fetch_word Ubsan.M.loaded_segments (0xa5020 : word) = Some W_a5020.
Proof. vm_refl. Qed.
Lemma D_a5020 : decode_any W_a5020 = Some (Branch BC_NE 15 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5024 : bv 32 := 0x00052783.
Lemma F_a5024 : fetch_word Ubsan.M.loaded_segments (0xa5024 : word) = Some W_a5024.
Proof. vm_refl. Qed.
Lemma D_a5024 : decode_any W_a5024 = Some (Load SZ4 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5028 : bv 32 := 0x00f5a023.
Lemma F_a5028 : fetch_word Ubsan.M.loaded_segments (0xa5028 : word) = Some W_a5028.
Proof. vm_refl. Qed.
Lemma D_a5028 : decode_any W_a5028 = Some (Store SZ4 11 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a502c : bv 32 := 0x00060a63.
Lemma F_a502c : fetch_word Ubsan.M.loaded_segments (0xa502c : word) = Some W_a502c.
Proof. vm_refl. Qed.
Lemma D_a502c : decode_any W_a502c = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5030 : bv 32 := 0x010365b3.
Lemma F_a5030 : fetch_word Ubsan.M.loaded_segments (0xa5030 : word) = Some W_a5030.
Proof. vm_refl. Qed.
Lemma D_a5030 : decode_any W_a5030 = Some (Op ALU_OR 11 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5034 : bv 32 := 0x06059c63.
Lemma F_a5034 : fetch_word Ubsan.M.loaded_segments (0xa5034 : word) = Some W_a5034.
Proof. vm_refl. Qed.
Lemma D_a5034 : decode_any W_a5034 = Some (Branch BC_NE 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5038 : bv 32 := 0x00452583.
Lemma F_a5038 : fetch_word Ubsan.M.loaded_segments (0xa5038 : word) = Some W_a5038.
Proof. vm_refl. Qed.
Lemma D_a5038 : decode_any W_a5038 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a503c : bv 32 := 0x00b62023.
Lemma F_a503c : fetch_word Ubsan.M.loaded_segments (0xa503c : word) = Some W_a503c.
Proof. vm_refl. Qed.
Lemma D_a503c : decode_any W_a503c = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5040 : bv 32 := 0x00068a63.
Lemma F_a5040 : fetch_word Ubsan.M.loaded_segments (0xa5040 : word) = Some W_a5040.
Proof. vm_refl. Qed.
Lemma D_a5040 : decode_any W_a5040 = Some (Branch BC_EQ 13 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5044 : bv 32 := 0x011365b3.
Lemma F_a5044 : fetch_word Ubsan.M.loaded_segments (0xa5044 : word) = Some W_a5044.
Proof. vm_refl. Qed.
Lemma D_a5044 : decode_any W_a5044 = Some (Op ALU_OR 11 6 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5048 : bv 32 := 0x06059263.
Lemma F_a5048 : fetch_word Ubsan.M.loaded_segments (0xa5048 : word) = Some W_a5048.
Proof. vm_refl. Qed.
Lemma D_a5048 : decode_any W_a5048 = Some (Branch BC_NE 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_a504c : bv 32 := 0x00852583.
Lemma F_a504c : fetch_word Ubsan.M.loaded_segments (0xa504c : word) = Some W_a504c.
Proof. vm_refl. Qed.
Lemma D_a504c : decode_any W_a504c = Some (Load SZ4 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5050 : bv 32 := 0x00b6a023.
Lemma F_a5050 : fetch_word Ubsan.M.loaded_segments (0xa5050 : word) = Some W_a5050.
Proof. vm_refl. Qed.
Lemma D_a5050 : decode_any W_a5050 = Some (Store SZ4 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5054 : bv 32 := 0x04070463.
Lemma F_a5054 : fetch_word Ubsan.M.loaded_segments (0xa5054 : word) = Some W_a5054.
Proof. vm_refl. Qed.
Lemma D_a5054 : decode_any W_a5054 = Some (Branch BC_EQ 14 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5058 : bv 32 := 0x005365b3.
Lemma F_a5058 : fetch_word Ubsan.M.loaded_segments (0xa5058 : word) = Some W_a5058.
Proof. vm_refl. Qed.
Lemma D_a5058 : decode_any W_a5058 = Some (Op ALU_OR 11 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a505c : bv 32 := 0x04059863.
Lemma F_a505c : fetch_word Ubsan.M.loaded_segments (0xa505c : word) = Some W_a505c.
Proof. vm_refl. Qed.
Lemma D_a505c : decode_any W_a505c = Some (Branch BC_NE 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5060 : bv 32 := 0x00c52503.
Lemma F_a5060 : fetch_word Ubsan.M.loaded_segments (0xa5060 : word) = Some W_a5060.
Proof. vm_refl. Qed.
Lemma D_a5060 : decode_any W_a5060 = Some (Load SZ4 true 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5064 : bv 32 := 0x00a72023.
Lemma F_a5064 : fetch_word Ubsan.M.loaded_segments (0xa5064 : word) = Some W_a5064.
Proof. vm_refl. Qed.
Lemma D_a5064 : decode_any W_a5064 = Some (Store SZ4 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5068 : bv 32 := 0x00058513.
Lemma F_a5068 : fetch_word Ubsan.M.loaded_segments (0xa5068 : word) = Some W_a5068.
Proof. vm_refl. Qed.
Lemma D_a5068 : decode_any W_a5068 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a506c : bv 32 := 0x00008067.
Lemma F_a506c : fetch_word Ubsan.M.loaded_segments (0xa506c : word) = Some W_a506c.
Proof. vm_refl. Qed.
Lemma D_a506c : decode_any W_a506c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5070 : bv 32 := 0x00082517.
Lemma F_a5070 : fetch_word Ubsan.M.loaded_segments (0xa5070 : word) = Some W_a5070.
Proof. vm_refl. Qed.
Lemma D_a5070 : decode_any W_a5070 = Some (Auipc 10 130, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5074 : bv 32 := 0xa0053503.
Lemma F_a5074 : fetch_word Ubsan.M.loaded_segments (0xa5074 : word) = Some W_a5074.
Proof. vm_refl. Qed.
Lemma D_a5074 : decode_any W_a5074 = Some (Load SZ8 true 10 10 2560, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5078 : bv 32 := 0x00052503.
Lemma F_a5078 : fetch_word Ubsan.M.loaded_segments (0xa5078 : word) = Some W_a5078.
Proof. vm_refl. Qed.
Lemma D_a5078 : decode_any W_a5078 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a507c : bv 32 := 0x00500593.
Lemma F_a507c : fetch_word Ubsan.M.loaded_segments (0xa507c : word) = Some W_a507c.
Proof. vm_refl. Qed.
Lemma D_a507c : decode_any W_a507c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5080 : bv 32 := 0x02a5c263.
Lemma F_a5080 : fetch_word Ubsan.M.loaded_segments (0xa5080 : word) = Some W_a5080.
Proof. vm_refl. Qed.
Lemma D_a5080 : decode_any W_a5080 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5084 : bv 32 := 0xfff72517.
Lemma F_a5084 : fetch_word Ubsan.M.loaded_segments (0xa5084 : word) = Some W_a5084.
Proof. vm_refl. Qed.
Lemma D_a5084 : decode_any W_a5084 = Some (Auipc 10 1048434, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5088 : bv 32 := 0xfff73597.
Lemma F_a5088 : fetch_word Ubsan.M.loaded_segments (0xa5088 : word) = Some W_a5088.
Proof. vm_refl. Qed.
Lemma D_a5088 : decode_any W_a5088 = Some (Auipc 11 1048435, 4%Z).
Proof. vm_refl. Qed.

Definition W_a508c : bv 32 := 0x18150513.
Lemma F_a508c : fetch_word Ubsan.M.loaded_segments (0xa508c : word) = Some W_a508c.
Proof. vm_refl. Qed.
Lemma D_a508c : decode_any W_a508c = Some (OpImm ALU_ADD 10 10 385, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5090 : bv 32 := 0x80b58593.
Lemma F_a5090 : fetch_word Ubsan.M.loaded_segments (0xa5090 : word) = Some W_a5090.
Proof. vm_refl. Qed.
Lemma D_a5090 : decode_any W_a5090 = Some (OpImm ALU_ADD 11 11 2059, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5094 : bv 32 := 0x00100613.
Lemma F_a5094 : fetch_word Ubsan.M.loaded_segments (0xa5094 : word) = Some W_a5094.
Proof. vm_refl. Qed.
Lemma D_a5094 : decode_any W_a5094 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5098 : bv 32 := 0xdd8be06f.
Lemma F_a5098 : fetch_word Ubsan.M.loaded_segments (0xa5098 : word) = Some W_a5098.
Proof. vm_refl. Qed.
Lemma D_a5098 : decode_any W_a5098 = Some (Jal 0 1828312, 4%Z).
Proof. vm_refl. Qed.

Definition W_a509c : bv 32 := 0x00000513.
Lemma F_a509c : fetch_word Ubsan.M.loaded_segments (0xa509c : word) = Some W_a509c.
Proof. vm_refl. Qed.
Lemma D_a509c : decode_any W_a509c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50a0 : bv 32 := 0x00008067.
Lemma F_a50a0 : fetch_word Ubsan.M.loaded_segments (0xa50a0 : word) = Some W_a50a0.
Proof. vm_refl. Qed.
Lemma D_a50a0 : decode_any W_a50a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50a4 : bv 32 := 0x00100513.
Lemma F_a50a4 : fetch_word Ubsan.M.loaded_segments (0xa50a4 : word) = Some W_a50a4.
Proof. vm_refl. Qed.
Lemma D_a50a4 : decode_any W_a50a4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50a8 : bv 32 := 0x00008067.
Lemma F_a50a8 : fetch_word Ubsan.M.loaded_segments (0xa50a8 : word) = Some W_a50a8.
Proof. vm_refl. Qed.
Lemma D_a50a8 : decode_any W_a50a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a50ac : bv 32 := 0xc0001073.
Lemma F_a50ac : fetch_word Ubsan.M.loaded_segments (0xa50ac : word) = Some W_a50ac.
Proof. vm_refl. Qed.
Lemma D_a50ac : decode_any W_a50ac = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
