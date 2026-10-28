(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1bba4 : bv 32 := 0xfb010113.
Lemma F_1bba4 : fetch_word Ubsan.M.loaded_segments (0x1cae0 : word) = Some W_1bba4.
Proof. vm_refl. Qed.
Lemma D_1bba4 : decode_any W_1bba4 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bba8 : bv 32 := 0x04113423.
Lemma F_1bba8 : fetch_word Ubsan.M.loaded_segments (0x1cae4 : word) = Some W_1bba8.
Proof. vm_refl. Qed.
Lemma D_1bba8 : decode_any W_1bba8 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbac : bv 32 := 0x04813023.
Lemma F_1bbac : fetch_word Ubsan.M.loaded_segments (0x1cae8 : word) = Some W_1bbac.
Proof. vm_refl. Qed.
Lemma D_1bbac : decode_any W_1bbac = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbb0 : bv 32 := 0x02913c23.
Lemma F_1bbb0 : fetch_word Ubsan.M.loaded_segments (0x1caec : word) = Some W_1bbb0.
Proof. vm_refl. Qed.
Lemma D_1bbb0 : decode_any W_1bbb0 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbb4 : bv 32 := 0x03213823.
Lemma F_1bbb4 : fetch_word Ubsan.M.loaded_segments (0x1caf0 : word) = Some W_1bbb4.
Proof. vm_refl. Qed.
Lemma D_1bbb4 : decode_any W_1bbb4 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbb8 : bv 32 := 0x03313423.
Lemma F_1bbb8 : fetch_word Ubsan.M.loaded_segments (0x1caf4 : word) = Some W_1bbb8.
Proof. vm_refl. Qed.
Lemma D_1bbb8 : decode_any W_1bbb8 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbbc : bv 32 := 0x0e050663.
Lemma F_1bbbc : fetch_word Ubsan.M.loaded_segments (0x1caf8 : word) = Some W_1bbbc.
Proof. vm_refl. Qed.
Lemma D_1bbbc : decode_any W_1bbbc = Some (Branch BC_EQ 10 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbc0 : bv 32 := 0x10058863.
Lemma F_1bbc0 : fetch_word Ubsan.M.loaded_segments (0x1cafc : word) = Some W_1bbc0.
Proof. vm_refl. Qed.
Lemma D_1bbc0 : decode_any W_1bbc0 = Some (Branch BC_EQ 11 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbc4 : bv 32 := 0x00060413.
Lemma F_1bbc4 : fetch_word Ubsan.M.loaded_segments (0x1cb00 : word) = Some W_1bbc4.
Proof. vm_refl. Qed.
Lemma D_1bbc4 : decode_any W_1bbc4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbc8 : bv 32 := 0x12060863.
Lemma F_1bbc8 : fetch_word Ubsan.M.loaded_segments (0x1cb04 : word) = Some W_1bbc8.
Proof. vm_refl. Qed.
Lemma D_1bbc8 : decode_any W_1bbc8 = Some (Branch BC_EQ 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbcc : bv 32 := 0x00058913.
Lemma F_1bbcc : fetch_word Ubsan.M.loaded_segments (0x1cb08 : word) = Some W_1bbcc.
Proof. vm_refl. Qed.
Lemma D_1bbcc : decode_any W_1bbcc = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbd0 : bv 32 := 0x02410593.
Lemma F_1bbd0 : fetch_word Ubsan.M.loaded_segments (0x1cb0c : word) = Some W_1bbd0.
Proof. vm_refl. Qed.
Lemma D_1bbd0 : decode_any W_1bbd0 = Some (OpImm ALU_ADD 11 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbd4 : bv 32 := 0x01810613.
Lemma F_1bbd4 : fetch_word Ubsan.M.loaded_segments (0x1cb10 : word) = Some W_1bbd4.
Proof. vm_refl. Qed.
Lemma D_1bbd4 : decode_any W_1bbd4 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbd8 : bv 32 := 0x00c10693.
Lemma F_1bbd8 : fetch_word Ubsan.M.loaded_segments (0x1cb14 : word) = Some W_1bbd8.
Proof. vm_refl. Qed.
Lemma D_1bbd8 : decode_any W_1bbd8 = Some (OpImm ALU_ADD 13 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbdc : bv 32 := 0x00050993.
Lemma F_1bbdc : fetch_word Ubsan.M.loaded_segments (0x1cb18 : word) = Some W_1bbdc.
Proof. vm_refl. Qed.
Lemma D_1bbdc : decode_any W_1bbdc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbe0 : bv 32 := 0x81cfd0ef.
Lemma F_1bbe0 : fetch_word Ubsan.M.loaded_segments (0x1cb1c : word) = Some W_1bbe0.
Proof. vm_refl. Qed.
Lemma D_1bbe0 : decode_any W_1bbe0 = Some (Jal 1 2084892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbe4 : bv 32 := 0x02010593.
Lemma F_1bbe4 : fetch_word Ubsan.M.loaded_segments (0x1cb20 : word) = Some W_1bbe4.
Proof. vm_refl. Qed.
Lemma D_1bbe4 : decode_any W_1bbe4 = Some (OpImm ALU_ADD 11 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbe8 : bv 32 := 0x01410613.
Lemma F_1bbe8 : fetch_word Ubsan.M.loaded_segments (0x1cb24 : word) = Some W_1bbe8.
Proof. vm_refl. Qed.
Lemma D_1bbe8 : decode_any W_1bbe8 = Some (OpImm ALU_ADD 12 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbec : bv 32 := 0x00810693.
Lemma F_1bbec : fetch_word Ubsan.M.loaded_segments (0x1cb28 : word) = Some W_1bbec.
Proof. vm_refl. Qed.
Lemma D_1bbec : decode_any W_1bbec = Some (OpImm ALU_ADD 13 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbf0 : bv 32 := 0x00090493.
Lemma F_1bbf0 : fetch_word Ubsan.M.loaded_segments (0x1cb2c : word) = Some W_1bbf0.
Proof. vm_refl. Qed.
Lemma D_1bbf0 : decode_any W_1bbf0 = Some (OpImm ALU_ADD 9 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbf4 : bv 32 := 0x00090513.
Lemma F_1bbf4 : fetch_word Ubsan.M.loaded_segments (0x1cb30 : word) = Some W_1bbf4.
Proof. vm_refl. Qed.
Lemma D_1bbf4 : decode_any W_1bbf4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbf8 : bv 32 := 0x804fd0ef.
Lemma F_1bbf8 : fetch_word Ubsan.M.loaded_segments (0x1cb34 : word) = Some W_1bbf8.
Proof. vm_refl. Qed.
Lemma D_1bbf8 : decode_any W_1bbf8 = Some (Jal 1 2084868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbfc : bv 32 := 0x01c10593.
Lemma F_1bbfc : fetch_word Ubsan.M.loaded_segments (0x1cb38 : word) = Some W_1bbfc.
Proof. vm_refl. Qed.
Lemma D_1bbfc : decode_any W_1bbfc = Some (OpImm ALU_ADD 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc00 : bv 32 := 0x01010613.
Lemma F_1bc00 : fetch_word Ubsan.M.loaded_segments (0x1cb3c : word) = Some W_1bc00.
Proof. vm_refl. Qed.
Lemma D_1bc00 : decode_any W_1bc00 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc04 : bv 32 := 0x00410693.
Lemma F_1bc04 : fetch_word Ubsan.M.loaded_segments (0x1cb40 : word) = Some W_1bc04.
Proof. vm_refl. Qed.
Lemma D_1bc04 : decode_any W_1bc04 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc08 : bv 32 := 0x00040513.
Lemma F_1bc08 : fetch_word Ubsan.M.loaded_segments (0x1cb44 : word) = Some W_1bc08.
Proof. vm_refl. Qed.
Lemma D_1bc08 : decode_any W_1bc08 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc0c : bv 32 := 0xff1fc0ef.
Lemma F_1bc0c : fetch_word Ubsan.M.loaded_segments (0x1cb48 : word) = Some W_1bc0c.
Proof. vm_refl. Qed.
Lemma D_1bc0c : decode_any W_1bc0c = Some (Jal 1 2084848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc10 : bv 32 := 0x00c12583.
Lemma F_1bc10 : fetch_word Ubsan.M.loaded_segments (0x1cb4c : word) = Some W_1bc10.
Proof. vm_refl. Qed.
Lemma D_1bc10 : decode_any W_1bc10 = Some (Load SZ4 true 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc14 : bv 32 := 0x00800513.
Lemma F_1bc14 : fetch_word Ubsan.M.loaded_segments (0x1cb50 : word) = Some W_1bc14.
Proof. vm_refl. Qed.
Lemma D_1bc14 : decode_any W_1bc14 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc18 : bv 32 := 0x12a59263.
Lemma F_1bc18 : fetch_word Ubsan.M.loaded_segments (0x1cb54 : word) = Some W_1bc18.
Proof. vm_refl. Qed.
Lemma D_1bc18 : decode_any W_1bc18 = Some (Branch BC_NE 11 10 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc1c : bv 32 := 0x00812583.
Lemma F_1bc1c : fetch_word Ubsan.M.loaded_segments (0x1cb58 : word) = Some W_1bc1c.
Proof. vm_refl. Qed.
Lemma D_1bc1c : decode_any W_1bc1c = Some (Load SZ4 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc20 : bv 32 := 0x10a59e63.
Lemma F_1bc20 : fetch_word Ubsan.M.loaded_segments (0x1cb5c : word) = Some W_1bc20.
Proof. vm_refl. Qed.
Lemma D_1bc20 : decode_any W_1bc20 = Some (Branch BC_NE 11 10 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc24 : bv 32 := 0x00412503.
Lemma F_1bc24 : fetch_word Ubsan.M.loaded_segments (0x1cb60 : word) = Some W_1bc24.
Proof. vm_refl. Qed.
Lemma D_1bc24 : decode_any W_1bc24 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc28 : bv 32 := 0x00800593.
Lemma F_1bc28 : fetch_word Ubsan.M.loaded_segments (0x1cb64 : word) = Some W_1bc28.
Proof. vm_refl. Qed.
Lemma D_1bc28 : decode_any W_1bc28 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc2c : bv 32 := 0x10b51863.
Lemma F_1bc2c : fetch_word Ubsan.M.loaded_segments (0x1cb68 : word) = Some W_1bc2c.
Proof. vm_refl. Qed.
Lemma D_1bc2c : decode_any W_1bc2c = Some (Branch BC_NE 10 11 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc30 : bv 32 := 0x02412503.
Lemma F_1bc30 : fetch_word Ubsan.M.loaded_segments (0x1cb6c : word) = Some W_1bc30.
Proof. vm_refl. Qed.
Lemma D_1bc30 : decode_any W_1bc30 = Some (Load SZ4 true 10 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc34 : bv 32 := 0x02012583.
Lemma F_1bc34 : fetch_word Ubsan.M.loaded_segments (0x1cb70 : word) = Some W_1bc34.
Proof. vm_refl. Qed.
Lemma D_1bc34 : decode_any W_1bc34 = Some (Load SZ4 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc38 : bv 32 := 0x12b51663.
Lemma F_1bc38 : fetch_word Ubsan.M.loaded_segments (0x1cb74 : word) = Some W_1bc38.
Proof. vm_refl. Qed.
Lemma D_1bc38 : decode_any W_1bc38 = Some (Branch BC_NE 10 11 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc3c : bv 32 := 0x01c12583.
Lemma F_1bc3c : fetch_word Ubsan.M.loaded_segments (0x1cb78 : word) = Some W_1bc3c.
Proof. vm_refl. Qed.
Lemma D_1bc3c : decode_any W_1bc3c = Some (Load SZ4 true 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc40 : bv 32 := 0x12b51263.
Lemma F_1bc40 : fetch_word Ubsan.M.loaded_segments (0x1cb7c : word) = Some W_1bc40.
Proof. vm_refl. Qed.
Lemma D_1bc40 : decode_any W_1bc40 = Some (Branch BC_NE 10 11 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc44 : bv 32 := 0x01812583.
Lemma F_1bc44 : fetch_word Ubsan.M.loaded_segments (0x1cb80 : word) = Some W_1bc44.
Proof. vm_refl. Qed.
Lemma D_1bc44 : decode_any W_1bc44 = Some (Load SZ4 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc48 : bv 32 := 0x01412603.
Lemma F_1bc48 : fetch_word Ubsan.M.loaded_segments (0x1cb84 : word) = Some W_1bc48.
Proof. vm_refl. Qed.
Lemma D_1bc48 : decode_any W_1bc48 = Some (Load SZ4 true 12 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc4c : bv 32 := 0x14c59063.
Lemma F_1bc4c : fetch_word Ubsan.M.loaded_segments (0x1cb88 : word) = Some W_1bc4c.
Proof. vm_refl. Qed.
Lemma D_1bc4c : decode_any W_1bc4c = Some (Branch BC_NE 11 12 320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc50 : bv 32 := 0x01012603.
Lemma F_1bc50 : fetch_word Ubsan.M.loaded_segments (0x1cb8c : word) = Some W_1bc50.
Proof. vm_refl. Qed.
Lemma D_1bc50 : decode_any W_1bc50 = Some (Load SZ4 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc54 : bv 32 := 0x12c59c63.
Lemma F_1bc54 : fetch_word Ubsan.M.loaded_segments (0x1cb90 : word) = Some W_1bc54.
Proof. vm_refl. Qed.
Lemma D_1bc54 : decode_any W_1bc54 = Some (Branch BC_NE 11 12 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc58 : bv 32 := 0x02000613.
Lemma F_1bc58 : fetch_word Ubsan.M.loaded_segments (0x1cb94 : word) = Some W_1bc58.
Proof. vm_refl. Qed.
Lemma D_1bc58 : decode_any W_1bc58 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc5c : bv 32 := 0xf38fc0ef.
Lemma F_1bc5c : fetch_word Ubsan.M.loaded_segments (0x1cb98 : word) = Some W_1bc5c.
Proof. vm_refl. Qed.
Lemma D_1bc5c : decode_any W_1bc5c = Some (Jal 1 2082616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc60 : bv 32 := 0x14050a63.
Lemma F_1bc60 : fetch_word Ubsan.M.loaded_segments (0x1cb9c : word) = Some W_1bc60.
Proof. vm_refl. Qed.
Lemma D_1bc60 : decode_any W_1bc60 = Some (Branch BC_EQ 10 0 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc64 : bv 32 := 0x00050913.
Lemma F_1bc64 : fetch_word Ubsan.M.loaded_segments (0x1cba0 : word) = Some W_1bc64.
Proof. vm_refl. Qed.
Lemma D_1bc64 : decode_any W_1bc64 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc68 : bv 32 := 0x00098593.
Lemma F_1bc68 : fetch_word Ubsan.M.loaded_segments (0x1cba4 : word) = Some W_1bc68.
Proof. vm_refl. Qed.
Lemma D_1bc68 : decode_any W_1bc68 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc6c : bv 32 := 0x84cfd0ef.
Lemma F_1bc6c : fetch_word Ubsan.M.loaded_segments (0x1cba8 : word) = Some W_1bc6c.
Proof. vm_refl. Qed.
Lemma D_1bc6c : decode_any W_1bc6c = Some (Jal 1 2084940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc70 : bv 32 := 0x00090513.
Lemma F_1bc70 : fetch_word Ubsan.M.loaded_segments (0x1cbac : word) = Some W_1bc70.
Proof. vm_refl. Qed.
Lemma D_1bc70 : decode_any W_1bc70 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc74 : bv 32 := 0x00098593.
Lemma F_1bc74 : fetch_word Ubsan.M.loaded_segments (0x1cbb0 : word) = Some W_1bc74.
Proof. vm_refl. Qed.
Lemma D_1bc74 : decode_any W_1bc74 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc78 : bv 32 := 0x00000613.
Lemma F_1bc78 : fetch_word Ubsan.M.loaded_segments (0x1cbb4 : word) = Some W_1bc78.
Proof. vm_refl. Qed.
Lemma D_1bc78 : decode_any W_1bc78 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc7c : bv 32 := 0xda5fe0ef.
Lemma F_1bc7c : fetch_word Ubsan.M.loaded_segments (0x1cbb8 : word) = Some W_1bc7c.
Proof. vm_refl. Qed.
Lemma D_1bc7c : decode_any W_1bc7c = Some (Jal 1 2092452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc80 : bv 32 := 0x00100613.
Lemma F_1bc80 : fetch_word Ubsan.M.loaded_segments (0x1cbbc : word) = Some W_1bc80.
Proof. vm_refl. Qed.
Lemma D_1bc80 : decode_any W_1bc80 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc84 : bv 32 := 0x00090513.
Lemma F_1bc84 : fetch_word Ubsan.M.loaded_segments (0x1cbc0 : word) = Some W_1bc84.
Proof. vm_refl. Qed.
Lemma D_1bc84 : decode_any W_1bc84 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc88 : bv 32 := 0x00048593.
Lemma F_1bc88 : fetch_word Ubsan.M.loaded_segments (0x1cbc4 : word) = Some W_1bc88.
Proof. vm_refl. Qed.
Lemma D_1bc88 : decode_any W_1bc88 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc8c : bv 32 := 0xd95fe0ef.
Lemma F_1bc8c : fetch_word Ubsan.M.loaded_segments (0x1cbc8 : word) = Some W_1bc8c.
Proof. vm_refl. Qed.
Lemma D_1bc8c : decode_any W_1bc8c = Some (Jal 1 2092436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc90 : bv 32 := 0x00200613.
Lemma F_1bc90 : fetch_word Ubsan.M.loaded_segments (0x1cbcc : word) = Some W_1bc90.
Proof. vm_refl. Qed.
Lemma D_1bc90 : decode_any W_1bc90 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc94 : bv 32 := 0x00090513.
Lemma F_1bc94 : fetch_word Ubsan.M.loaded_segments (0x1cbd0 : word) = Some W_1bc94.
Proof. vm_refl. Qed.
Lemma D_1bc94 : decode_any W_1bc94 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc98 : bv 32 := 0x00040593.
Lemma F_1bc98 : fetch_word Ubsan.M.loaded_segments (0x1cbd4 : word) = Some W_1bc98.
Proof. vm_refl. Qed.
Lemma D_1bc98 : decode_any W_1bc98 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc9c : bv 32 := 0xd85fe0ef.
Lemma F_1bc9c : fetch_word Ubsan.M.loaded_segments (0x1cbd8 : word) = Some W_1bc9c.
Proof. vm_refl. Qed.
Lemma D_1bc9c : decode_any W_1bc9c = Some (Jal 1 2092420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bca0 : bv 32 := 0x00090513.
Lemma F_1bca0 : fetch_word Ubsan.M.loaded_segments (0x1cbdc : word) = Some W_1bca0.
Proof. vm_refl. Qed.
Lemma D_1bca0 : decode_any W_1bca0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bca4 : bv 32 := 0x1440006f.
Lemma F_1bca4 : fetch_word Ubsan.M.loaded_segments (0x1cbe0 : word) = Some W_1bca4.
Proof. vm_refl. Qed.
Lemma D_1bca4 : decode_any W_1bca4 = Some (Jal 0 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bca8 : bv 32 := 0x00028517.
Lemma F_1bca8 : fetch_word Ubsan.M.loaded_segments (0x1cbe4 : word) = Some W_1bca8.
Proof. vm_refl. Qed.
Lemma D_1bca8 : decode_any W_1bca8 = Some (Auipc 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcac : bv 32 := 0x2b453503.
Lemma F_1bcac : fetch_word Ubsan.M.loaded_segments (0x1cbe8 : word) = Some W_1bcac.
Proof. vm_refl. Qed.
Lemma D_1bcac : decode_any W_1bcac = Some (Load SZ8 true 10 10 692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcb0 : bv 32 := 0x00052503.
Lemma F_1bcb0 : fetch_word Ubsan.M.loaded_segments (0x1cbec : word) = Some W_1bcb0.
Proof. vm_refl. Qed.
Lemma D_1bcb0 : decode_any W_1bcb0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcb4 : bv 32 := 0x00500593.
Lemma F_1bcb4 : fetch_word Ubsan.M.loaded_segments (0x1cbf0 : word) = Some W_1bcb4.
Proof. vm_refl. Qed.
Lemma D_1bcb4 : decode_any W_1bcb4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcb8 : bv 32 := 0x12a5c663.
Lemma F_1bcb8 : fetch_word Ubsan.M.loaded_segments (0x1cbf4 : word) = Some W_1bcb8.
Proof. vm_refl. Qed.
Lemma D_1bcb8 : decode_any W_1bcb8 = Some (Branch BC_LT 11 10 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcbc : bv 32 := 0xffff5517.
Lemma F_1bcbc : fetch_word Ubsan.M.loaded_segments (0x1cbf8 : word) = Some W_1bcbc.
Proof. vm_refl. Qed.
Lemma D_1bcbc : decode_any W_1bcbc = Some (Auipc 10 1048565, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcc0 : bv 32 := 0xffff4597.
Lemma F_1bcc0 : fetch_word Ubsan.M.loaded_segments (0x1cbfc : word) = Some W_1bcc0.
Proof. vm_refl. Qed.
Lemma D_1bcc0 : decode_any W_1bcc0 = Some (Auipc 11 1048564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcc4 : bv 32 := 0xc1e50513.
Lemma F_1bcc4 : fetch_word Ubsan.M.loaded_segments (0x1cc00 : word) = Some W_1bcc4.
Proof. vm_refl. Qed.
Lemma D_1bcc4 : decode_any W_1bcc4 = Some (OpImm ALU_ADD 10 10 3102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcc8 : bv 32 := 0x41158593.
Lemma F_1bcc8 : fetch_word Ubsan.M.loaded_segments (0x1cc04 : word) = Some W_1bcc8.
Proof. vm_refl. Qed.
Lemma D_1bcc8 : decode_any W_1bcc8 = Some (OpImm ALU_ADD 11 11 1041, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bccc : bv 32 := 0x0500006f.
Lemma F_1bccc : fetch_word Ubsan.M.loaded_segments (0x1cc08 : word) = Some W_1bccc.
Proof. vm_refl. Qed.
Lemma D_1bccc : decode_any W_1bccc = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcd0 : bv 32 := 0x00028517.
Lemma F_1bcd0 : fetch_word Ubsan.M.loaded_segments (0x1cc0c : word) = Some W_1bcd0.
Proof. vm_refl. Qed.
Lemma D_1bcd0 : decode_any W_1bcd0 = Some (Auipc 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcd4 : bv 32 := 0x28c53503.
Lemma F_1bcd4 : fetch_word Ubsan.M.loaded_segments (0x1cc10 : word) = Some W_1bcd4.
Proof. vm_refl. Qed.
Lemma D_1bcd4 : decode_any W_1bcd4 = Some (Load SZ8 true 10 10 652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcd8 : bv 32 := 0x00052503.
Lemma F_1bcd8 : fetch_word Ubsan.M.loaded_segments (0x1cc14 : word) = Some W_1bcd8.
Proof. vm_refl. Qed.
Lemma D_1bcd8 : decode_any W_1bcd8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcdc : bv 32 := 0x00500593.
Lemma F_1bcdc : fetch_word Ubsan.M.loaded_segments (0x1cc18 : word) = Some W_1bcdc.
Proof. vm_refl. Qed.
Lemma D_1bcdc : decode_any W_1bcdc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bce0 : bv 32 := 0x10a5c263.
Lemma F_1bce0 : fetch_word Ubsan.M.loaded_segments (0x1cc1c : word) = Some W_1bce0.
Proof. vm_refl. Qed.
Lemma D_1bce0 : decode_any W_1bce0 = Some (Branch BC_LT 11 10 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bce4 : bv 32 := 0xffff4517.
Lemma F_1bce4 : fetch_word Ubsan.M.loaded_segments (0x1cc20 : word) = Some W_1bce4.
Proof. vm_refl. Qed.
Lemma D_1bce4 : decode_any W_1bce4 = Some (Auipc 10 1048564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bce8 : bv 32 := 0xffff4597.
Lemma F_1bce8 : fetch_word Ubsan.M.loaded_segments (0x1cc24 : word) = Some W_1bce8.
Proof. vm_refl. Qed.
Lemma D_1bce8 : decode_any W_1bce8 = Some (Auipc 11 1048564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcec : bv 32 := 0x3ff50513.
Lemma F_1bcec : fetch_word Ubsan.M.loaded_segments (0x1cc28 : word) = Some W_1bcec.
Proof. vm_refl. Qed.
Lemma D_1bcec : decode_any W_1bcec = Some (OpImm ALU_ADD 10 10 1023, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcf0 : bv 32 := 0x3e958593.
Lemma F_1bcf0 : fetch_word Ubsan.M.loaded_segments (0x1cc2c : word) = Some W_1bcf0.
Proof. vm_refl. Qed.
Lemma D_1bcf0 : decode_any W_1bcf0 = Some (OpImm ALU_ADD 11 11 1001, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcf4 : bv 32 := 0x0280006f.
Lemma F_1bcf4 : fetch_word Ubsan.M.loaded_segments (0x1cc30 : word) = Some W_1bcf4.
Proof. vm_refl. Qed.
Lemma D_1bcf4 : decode_any W_1bcf4 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcf8 : bv 32 := 0x00028517.
Lemma F_1bcf8 : fetch_word Ubsan.M.loaded_segments (0x1cc34 : word) = Some W_1bcf8.
Proof. vm_refl. Qed.
Lemma D_1bcf8 : decode_any W_1bcf8 = Some (Auipc 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcfc : bv 32 := 0x26453503.
Lemma F_1bcfc : fetch_word Ubsan.M.loaded_segments (0x1cc38 : word) = Some W_1bcfc.
Proof. vm_refl. Qed.
Lemma D_1bcfc : decode_any W_1bcfc = Some (Load SZ8 true 10 10 612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd00 : bv 32 := 0x00052503.
Lemma F_1bd00 : fetch_word Ubsan.M.loaded_segments (0x1cc3c : word) = Some W_1bd00.
Proof. vm_refl. Qed.
Lemma D_1bd00 : decode_any W_1bd00 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd04 : bv 32 := 0x00500593.
Lemma F_1bd04 : fetch_word Ubsan.M.loaded_segments (0x1cc40 : word) = Some W_1bd04.
Proof. vm_refl. Qed.
Lemma D_1bd04 : decode_any W_1bd04 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd08 : bv 32 := 0x0ca5ce63.
Lemma F_1bd08 : fetch_word Ubsan.M.loaded_segments (0x1cc44 : word) = Some W_1bd08.
Proof. vm_refl. Qed.
Lemma D_1bd08 : decode_any W_1bd08 = Some (Branch BC_LT 11 10 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd0c : bv 32 := 0xffff5517.
Lemma F_1bd0c : fetch_word Ubsan.M.loaded_segments (0x1cc48 : word) = Some W_1bd0c.
Proof. vm_refl. Qed.
Lemma D_1bd0c : decode_any W_1bd0c = Some (Auipc 10 1048565, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd10 : bv 32 := 0xffff4597.
Lemma F_1bd10 : fetch_word Ubsan.M.loaded_segments (0x1cc4c : word) = Some W_1bd10.
Proof. vm_refl. Qed.
Lemma D_1bd10 : decode_any W_1bd10 = Some (Auipc 11 1048564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd14 : bv 32 := 0xfef50513.
Lemma F_1bd14 : fetch_word Ubsan.M.loaded_segments (0x1cc50 : word) = Some W_1bd14.
Proof. vm_refl. Qed.
Lemma D_1bd14 : decode_any W_1bd14 = Some (OpImm ALU_ADD 10 10 4079, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd18 : bv 32 := 0x3c158593.
Lemma F_1bd18 : fetch_word Ubsan.M.loaded_segments (0x1cc54 : word) = Some W_1bd18.
Proof. vm_refl. Qed.
Lemma D_1bd18 : decode_any W_1bd18 = Some (OpImm ALU_ADD 11 11 961, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd1c : bv 32 := 0x00000613.
Lemma F_1bd1c : fetch_word Ubsan.M.loaded_segments (0x1cc58 : word) = Some W_1bd1c.
Proof. vm_refl. Qed.
Lemma D_1bd1c : decode_any W_1bd1c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd20 : bv 32 := 0x04813083.
Lemma F_1bd20 : fetch_word Ubsan.M.loaded_segments (0x1cc5c : word) = Some W_1bd20.
Proof. vm_refl. Qed.
Lemma D_1bd20 : decode_any W_1bd20 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd24 : bv 32 := 0x04013403.
Lemma F_1bd24 : fetch_word Ubsan.M.loaded_segments (0x1cc60 : word) = Some W_1bd24.
Proof. vm_refl. Qed.
Lemma D_1bd24 : decode_any W_1bd24 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd28 : bv 32 := 0x03813483.
Lemma F_1bd28 : fetch_word Ubsan.M.loaded_segments (0x1cc64 : word) = Some W_1bd28.
Proof. vm_refl. Qed.
Lemma D_1bd28 : decode_any W_1bd28 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd2c : bv 32 := 0x03013903.
Lemma F_1bd2c : fetch_word Ubsan.M.loaded_segments (0x1cc68 : word) = Some W_1bd2c.
Proof. vm_refl. Qed.
Lemma D_1bd2c : decode_any W_1bd2c = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd30 : bv 32 := 0x02813983.
Lemma F_1bd30 : fetch_word Ubsan.M.loaded_segments (0x1cc6c : word) = Some W_1bd30.
Proof. vm_refl. Qed.
Lemma D_1bd30 : decode_any W_1bd30 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd34 : bv 32 := 0x05010113.
Lemma F_1bd34 : fetch_word Ubsan.M.loaded_segments (0x1cc70 : word) = Some W_1bd34.
Proof. vm_refl. Qed.
Lemma D_1bd34 : decode_any W_1bd34 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd38 : bv 32 := 0xa50fb06f.
Lemma F_1bd38 : fetch_word Ubsan.M.loaded_segments (0x1cc74 : word) = Some W_1bd38.
Proof. vm_refl. Qed.
Lemma D_1bd38 : decode_any W_1bd38 = Some (Jal 0 2077264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bde8 : bv 32 := 0x04813083.
Lemma F_1bde8 : fetch_word Ubsan.M.loaded_segments (0x1cd24 : word) = Some W_1bde8.
Proof. vm_refl. Qed.
Lemma D_1bde8 : decode_any W_1bde8 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdec : bv 32 := 0x04013403.
Lemma F_1bdec : fetch_word Ubsan.M.loaded_segments (0x1cd28 : word) = Some W_1bdec.
Proof. vm_refl. Qed.
Lemma D_1bdec : decode_any W_1bdec = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdf0 : bv 32 := 0x03813483.
Lemma F_1bdf0 : fetch_word Ubsan.M.loaded_segments (0x1cd2c : word) = Some W_1bdf0.
Proof. vm_refl. Qed.
Lemma D_1bdf0 : decode_any W_1bdf0 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdf4 : bv 32 := 0x03013903.
Lemma F_1bdf4 : fetch_word Ubsan.M.loaded_segments (0x1cd30 : word) = Some W_1bdf4.
Proof. vm_refl. Qed.
Lemma D_1bdf4 : decode_any W_1bdf4 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdf8 : bv 32 := 0x02813983.
Lemma F_1bdf8 : fetch_word Ubsan.M.loaded_segments (0x1cd34 : word) = Some W_1bdf8.
Proof. vm_refl. Qed.
Lemma D_1bdf8 : decode_any W_1bdf8 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdfc : bv 32 := 0x05010113.
Lemma F_1bdfc : fetch_word Ubsan.M.loaded_segments (0x1cd38 : word) = Some W_1bdfc.
Proof. vm_refl. Qed.
Lemma D_1bdfc : decode_any W_1bdfc = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be00 : bv 32 := 0x00008067.
Lemma F_1be00 : fetch_word Ubsan.M.loaded_segments (0x1cd3c : word) = Some W_1be00.
Proof. vm_refl. Qed.
Lemma D_1be00 : decode_any W_1be00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
