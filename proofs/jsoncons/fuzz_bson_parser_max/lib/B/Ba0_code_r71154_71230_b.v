(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8afcc : bv 32 := 0x02060063.
Lemma F_8afcc : fetch_word AsanUbsan.M.loaded_segments (0x8b3e4 : word) = Some W_8afcc.
Proof. vm_refl. Qed.
Lemma D_8afcc : decode_any W_8afcc = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8afd0 : bv 32 := 0x00c50633.
Lemma F_8afd0 : fetch_word AsanUbsan.M.loaded_segments (0x8b3e8 : word) = Some W_8afd0.
Proof. vm_refl. Qed.
Lemma D_8afd0 : decode_any W_8afd0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8afd4 : bv 32 := 0x00050693.
Lemma F_8afd4 : fetch_word AsanUbsan.M.loaded_segments (0x8b3ec : word) = Some W_8afd4.
Proof. vm_refl. Qed.
Lemma D_8afd4 : decode_any W_8afd4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8afd8 : bv 32 := 0x0005c703.
Lemma F_8afd8 : fetch_word AsanUbsan.M.loaded_segments (0x8b3f0 : word) = Some W_8afd8.
Proof. vm_refl. Qed.
Lemma D_8afd8 : decode_any W_8afd8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8afdc : bv 32 := 0x00e68023.
Lemma F_8afdc : fetch_word AsanUbsan.M.loaded_segments (0x8b3f4 : word) = Some W_8afdc.
Proof. vm_refl. Qed.
Lemma D_8afdc : decode_any W_8afdc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8afe0 : bv 32 := 0x00168693.
Lemma F_8afe0 : fetch_word AsanUbsan.M.loaded_segments (0x8b3f8 : word) = Some W_8afe0.
Proof. vm_refl. Qed.
Lemma D_8afe0 : decode_any W_8afe0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8afe4 : bv 32 := 0x00158593.
Lemma F_8afe4 : fetch_word AsanUbsan.M.loaded_segments (0x8b3fc : word) = Some W_8afe4.
Proof. vm_refl. Qed.
Lemma D_8afe4 : decode_any W_8afe4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8afe8 : bv 32 := 0xfec698e3.
Lemma F_8afe8 : fetch_word AsanUbsan.M.loaded_segments (0x8b400 : word) = Some W_8afe8.
Proof. vm_refl. Qed.
Lemma D_8afe8 : decode_any W_8afe8 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8afec : bv 32 := 0x00008067.
Lemma F_8afec : fetch_word AsanUbsan.M.loaded_segments (0x8b404 : word) = Some W_8afec.
Proof. vm_refl. Qed.
Lemma D_8afec : decode_any W_8afec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8aff0 : bv 32 := 0x02b57463.
Lemma F_8aff0 : fetch_word AsanUbsan.M.loaded_segments (0x8b408 : word) = Some W_8aff0.
Proof. vm_refl. Qed.
Lemma D_8aff0 : decode_any W_8aff0 = Some (Branch BC_GEU 10 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8aff4 : bv 32 := 0x04c05863.
Lemma F_8aff4 : fetch_word AsanUbsan.M.loaded_segments (0x8b40c : word) = Some W_8aff4.
Proof. vm_refl. Qed.
Lemma D_8aff4 : decode_any W_8aff4 = Some (Branch BC_GE 0 12 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8aff8 : bv 32 := 0x00c50633.
Lemma F_8aff8 : fetch_word AsanUbsan.M.loaded_segments (0x8b410 : word) = Some W_8aff8.
Proof. vm_refl. Qed.
Lemma D_8aff8 : decode_any W_8aff8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8affc : bv 32 := 0x00050693.
Lemma F_8affc : fetch_word AsanUbsan.M.loaded_segments (0x8b414 : word) = Some W_8affc.
Proof. vm_refl. Qed.
Lemma D_8affc : decode_any W_8affc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b000 : bv 32 := 0x0005c703.
Lemma F_8b000 : fetch_word AsanUbsan.M.loaded_segments (0x8b418 : word) = Some W_8b000.
Proof. vm_refl. Qed.
Lemma D_8b000 : decode_any W_8b000 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b004 : bv 32 := 0x00e68023.
Lemma F_8b004 : fetch_word AsanUbsan.M.loaded_segments (0x8b41c : word) = Some W_8b004.
Proof. vm_refl. Qed.
Lemma D_8b004 : decode_any W_8b004 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b008 : bv 32 := 0x00168693.
Lemma F_8b008 : fetch_word AsanUbsan.M.loaded_segments (0x8b420 : word) = Some W_8b008.
Proof. vm_refl. Qed.
Lemma D_8b008 : decode_any W_8b008 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b00c : bv 32 := 0x00158593.
Lemma F_8b00c : fetch_word AsanUbsan.M.loaded_segments (0x8b424 : word) = Some W_8b00c.
Proof. vm_refl. Qed.
Lemma D_8b00c : decode_any W_8b00c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b010 : bv 32 := 0xfec698e3.
Lemma F_8b010 : fetch_word AsanUbsan.M.loaded_segments (0x8b428 : word) = Some W_8b010.
Proof. vm_refl. Qed.
Lemma D_8b010 : decode_any W_8b010 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b014 : bv 32 := 0x0300006f.
Lemma F_8b014 : fetch_word AsanUbsan.M.loaded_segments (0x8b42c : word) = Some W_8b014.
Proof. vm_refl. Qed.
Lemma D_8b014 : decode_any W_8b014 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b018 : bv 32 := 0x02a5f663.
Lemma F_8b018 : fetch_word AsanUbsan.M.loaded_segments (0x8b430 : word) = Some W_8b018.
Proof. vm_refl. Qed.
Lemma D_8b018 : decode_any W_8b018 = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b01c : bv 32 := 0x02c05463.
Lemma F_8b01c : fetch_word AsanUbsan.M.loaded_segments (0x8b434 : word) = Some W_8b01c.
Proof. vm_refl. Qed.
Lemma D_8b01c : decode_any W_8b01c = Some (Branch BC_GE 0 12 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b020 : bv 32 := 0xfff60693.
Lemma F_8b020 : fetch_word AsanUbsan.M.loaded_segments (0x8b438 : word) = Some W_8b020.
Proof. vm_refl. Qed.
Lemma D_8b020 : decode_any W_8b020 = Some (OpImm ALU_ADD 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b024 : bv 32 := 0x00100613.
Lemma F_8b024 : fetch_word AsanUbsan.M.loaded_segments (0x8b43c : word) = Some W_8b024.
Proof. vm_refl. Qed.
Lemma D_8b024 : decode_any W_8b024 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b028 : bv 32 := 0x00d58733.
Lemma F_8b028 : fetch_word AsanUbsan.M.loaded_segments (0x8b440 : word) = Some W_8b028.
Proof. vm_refl. Qed.
Lemma D_8b028 : decode_any W_8b028 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b02c : bv 32 := 0x00074703.
Lemma F_8b02c : fetch_word AsanUbsan.M.loaded_segments (0x8b444 : word) = Some W_8b02c.
Proof. vm_refl. Qed.
Lemma D_8b02c : decode_any W_8b02c = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b030 : bv 32 := 0x00d507b3.
Lemma F_8b030 : fetch_word AsanUbsan.M.loaded_segments (0x8b448 : word) = Some W_8b030.
Proof. vm_refl. Qed.
Lemma D_8b030 : decode_any W_8b030 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b034 : bv 32 := 0x00168813.
Lemma F_8b034 : fetch_word AsanUbsan.M.loaded_segments (0x8b44c : word) = Some W_8b034.
Proof. vm_refl. Qed.
Lemma D_8b034 : decode_any W_8b034 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b038 : bv 32 := 0xfff68693.
Lemma F_8b038 : fetch_word AsanUbsan.M.loaded_segments (0x8b450 : word) = Some W_8b038.
Proof. vm_refl. Qed.
Lemma D_8b038 : decode_any W_8b038 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b03c : bv 32 := 0x00e78023.
Lemma F_8b03c : fetch_word AsanUbsan.M.loaded_segments (0x8b454 : word) = Some W_8b03c.
Proof. vm_refl. Qed.
Lemma D_8b03c : decode_any W_8b03c = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b040 : bv 32 := 0xff0664e3.
Lemma F_8b040 : fetch_word AsanUbsan.M.loaded_segments (0x8b458 : word) = Some W_8b040.
Proof. vm_refl. Qed.
Lemma D_8b040 : decode_any W_8b040 = Some (Branch BC_LTU 12 16 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b044 : bv 32 := 0x00008067.
Lemma F_8b044 : fetch_word AsanUbsan.M.loaded_segments (0x8b45c : word) = Some W_8b044.
Proof. vm_refl. Qed.
Lemma D_8b044 : decode_any W_8b044 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b048 : bv 32 := 0x00a666b3.
Lemma F_8b048 : fetch_word AsanUbsan.M.loaded_segments (0x8b460 : word) = Some W_8b048.
Proof. vm_refl. Qed.
Lemma D_8b048 : decode_any W_8b048 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b04c : bv 32 := 0x00f6f693.
Lemma F_8b04c : fetch_word AsanUbsan.M.loaded_segments (0x8b464 : word) = Some W_8b04c.
Proof. vm_refl. Qed.
Lemma D_8b04c : decode_any W_8b04c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b050 : bv 32 := 0x02068063.
Lemma F_8b050 : fetch_word AsanUbsan.M.loaded_segments (0x8b468 : word) = Some W_8b050.
Proof. vm_refl. Qed.
Lemma D_8b050 : decode_any W_8b050 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b054 : bv 32 := 0x04060863.
Lemma F_8b054 : fetch_word AsanUbsan.M.loaded_segments (0x8b46c : word) = Some W_8b054.
Proof. vm_refl. Qed.
Lemma D_8b054 : decode_any W_8b054 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b058 : bv 32 := 0x00c50633.
Lemma F_8b058 : fetch_word AsanUbsan.M.loaded_segments (0x8b470 : word) = Some W_8b058.
Proof. vm_refl. Qed.
Lemma D_8b058 : decode_any W_8b058 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b05c : bv 32 := 0x00050693.
Lemma F_8b05c : fetch_word AsanUbsan.M.loaded_segments (0x8b474 : word) = Some W_8b05c.
Proof. vm_refl. Qed.
Lemma D_8b05c : decode_any W_8b05c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b060 : bv 32 := 0x00b68023.
Lemma F_8b060 : fetch_word AsanUbsan.M.loaded_segments (0x8b478 : word) = Some W_8b060.
Proof. vm_refl. Qed.
Lemma D_8b060 : decode_any W_8b060 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b064 : bv 32 := 0x00168693.
Lemma F_8b064 : fetch_word AsanUbsan.M.loaded_segments (0x8b47c : word) = Some W_8b064.
Proof. vm_refl. Qed.
Lemma D_8b064 : decode_any W_8b064 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b068 : bv 32 := 0xfec69ce3.
Lemma F_8b068 : fetch_word AsanUbsan.M.loaded_segments (0x8b480 : word) = Some W_8b068.
Proof. vm_refl. Qed.
Lemma D_8b068 : decode_any W_8b068 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b06c : bv 32 := 0x0380006f.
Lemma F_8b06c : fetch_word AsanUbsan.M.loaded_segments (0x8b484 : word) = Some W_8b06c.
Proof. vm_refl. Qed.
Lemma D_8b06c : decode_any W_8b06c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b070 : bv 32 := 0x02060a63.
Lemma F_8b070 : fetch_word AsanUbsan.M.loaded_segments (0x8b488 : word) = Some W_8b070.
Proof. vm_refl. Qed.
Lemma D_8b070 : decode_any W_8b070 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b074 : bv 32 := 0x00c50633.
Lemma F_8b074 : fetch_word AsanUbsan.M.loaded_segments (0x8b48c : word) = Some W_8b074.
Proof. vm_refl. Qed.
Lemma D_8b074 : decode_any W_8b074 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b078 : bv 32 := 0x00859693.
Lemma F_8b078 : fetch_word AsanUbsan.M.loaded_segments (0x8b490 : word) = Some W_8b078.
Proof. vm_refl. Qed.
Lemma D_8b078 : decode_any W_8b078 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b07c : bv 32 := 0x00b6e5b3.
Lemma F_8b07c : fetch_word AsanUbsan.M.loaded_segments (0x8b494 : word) = Some W_8b07c.
Proof. vm_refl. Qed.
Lemma D_8b07c : decode_any W_8b07c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b080 : bv 32 := 0x01059693.
Lemma F_8b080 : fetch_word AsanUbsan.M.loaded_segments (0x8b498 : word) = Some W_8b080.
Proof. vm_refl. Qed.
Lemma D_8b080 : decode_any W_8b080 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b084 : bv 32 := 0x00b6e5b3.
Lemma F_8b084 : fetch_word AsanUbsan.M.loaded_segments (0x8b49c : word) = Some W_8b084.
Proof. vm_refl. Qed.
Lemma D_8b084 : decode_any W_8b084 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b088 : bv 32 := 0x02059693.
Lemma F_8b088 : fetch_word AsanUbsan.M.loaded_segments (0x8b4a0 : word) = Some W_8b088.
Proof. vm_refl. Qed.
Lemma D_8b088 : decode_any W_8b088 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b08c : bv 32 := 0x00b6e5b3.
Lemma F_8b08c : fetch_word AsanUbsan.M.loaded_segments (0x8b4a4 : word) = Some W_8b08c.
Proof. vm_refl. Qed.
Lemma D_8b08c : decode_any W_8b08c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b090 : bv 32 := 0x00050693.
Lemma F_8b090 : fetch_word AsanUbsan.M.loaded_segments (0x8b4a8 : word) = Some W_8b090.
Proof. vm_refl. Qed.
Lemma D_8b090 : decode_any W_8b090 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b094 : bv 32 := 0x00b6b023.
Lemma F_8b094 : fetch_word AsanUbsan.M.loaded_segments (0x8b4ac : word) = Some W_8b094.
Proof. vm_refl. Qed.
Lemma D_8b094 : decode_any W_8b094 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b098 : bv 32 := 0x00b6b423.
Lemma F_8b098 : fetch_word AsanUbsan.M.loaded_segments (0x8b4b0 : word) = Some W_8b098.
Proof. vm_refl. Qed.
Lemma D_8b098 : decode_any W_8b098 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b09c : bv 32 := 0x01068693.
Lemma F_8b09c : fetch_word AsanUbsan.M.loaded_segments (0x8b4b4 : word) = Some W_8b09c.
Proof. vm_refl. Qed.
Lemma D_8b09c : decode_any W_8b09c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b0a0 : bv 32 := 0xfec6eae3.
Lemma F_8b0a0 : fetch_word AsanUbsan.M.loaded_segments (0x8b4b8 : word) = Some W_8b0a0.
Proof. vm_refl. Qed.
Lemma D_8b0a0 : decode_any W_8b0a0 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b0a4 : bv 32 := 0x00008067.
Lemma F_8b0a4 : fetch_word AsanUbsan.M.loaded_segments (0x8b4bc : word) = Some W_8b0a4.
Proof. vm_refl. Qed.
Lemma D_8b0a4 : decode_any W_8b0a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
