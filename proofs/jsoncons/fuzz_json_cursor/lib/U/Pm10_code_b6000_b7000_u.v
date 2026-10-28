(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_b6000 : bv 32 := 0x00c5a423.
Lemma F_b6000 : fetch_word Ubsan.M.loaded_segments (0xb7e90 : word) = Some W_b6000.
Proof. vm_refl. Qed.
Lemma D_b6000 : decode_any W_b6000 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6004 : bv 32 := 0x01900793.
Lemma F_b6004 : fetch_word Ubsan.M.loaded_segments (0xb7e94 : word) = Some W_b6004.
Proof. vm_refl. Qed.
Lemma D_b6004 : decode_any W_b6004 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6008 : bv 32 := 0xfec6aa23.
Lemma F_b6008 : fetch_word Ubsan.M.loaded_segments (0xb7e98 : word) = Some W_b6008.
Proof. vm_refl. Qed.
Lemma D_b6008 : decode_any W_b6008 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_b600c : bv 32 := 0xfec6ac23.
Lemma F_b600c : fetch_word Ubsan.M.loaded_segments (0xb7e9c : word) = Some W_b600c.
Proof. vm_refl. Qed.
Lemma D_b600c : decode_any W_b600c = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6010 : bv 32 := 0x06f76463.
Lemma F_b6010 : fetch_word Ubsan.M.loaded_segments (0xb7ea0 : word) = Some W_b6010.
Proof. vm_refl. Qed.
Lemma D_b6010 : decode_any W_b6010 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6014 : bv 32 := 0x00c5a623.
Lemma F_b6014 : fetch_word Ubsan.M.loaded_segments (0xb7ea4 : word) = Some W_b6014.
Proof. vm_refl. Qed.
Lemma D_b6014 : decode_any W_b6014 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6018 : bv 32 := 0x00c5a823.
Lemma F_b6018 : fetch_word Ubsan.M.loaded_segments (0xb7ea8 : word) = Some W_b6018.
Proof. vm_refl. Qed.
Lemma D_b6018 : decode_any W_b6018 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b601c : bv 32 := 0x00c5aa23.
Lemma F_b601c : fetch_word Ubsan.M.loaded_segments (0xb7eac : word) = Some W_b601c.
Proof. vm_refl. Qed.
Lemma D_b601c : decode_any W_b601c = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6020 : bv 32 := 0x00c5ac23.
Lemma F_b6020 : fetch_word Ubsan.M.loaded_segments (0xb7eb0 : word) = Some W_b6020.
Proof. vm_refl. Qed.
Lemma D_b6020 : decode_any W_b6020 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6024 : bv 32 := 0x0045f793.
Lemma F_b6024 : fetch_word Ubsan.M.loaded_segments (0xb7eb4 : word) = Some W_b6024.
Proof. vm_refl. Qed.
Lemma D_b6024 : decode_any W_b6024 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6028 : bv 32 := 0x02000813.
Lemma F_b6028 : fetch_word Ubsan.M.loaded_segments (0xb7eb8 : word) = Some W_b6028.
Proof. vm_refl. Qed.
Lemma D_b6028 : decode_any W_b6028 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_b602c : bv 32 := 0x01878793.
Lemma F_b602c : fetch_word Ubsan.M.loaded_segments (0xb7ebc : word) = Some W_b602c.
Proof. vm_refl. Qed.
Lemma D_b602c : decode_any W_b602c = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6030 : bv 32 := 0x40f70733.
Lemma F_b6030 : fetch_word Ubsan.M.loaded_segments (0xb7ec0 : word) = Some W_b6030.
Proof. vm_refl. Qed.
Lemma D_b6030 : decode_any W_b6030 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6034 : bv 32 := 0xfec6a223.
Lemma F_b6034 : fetch_word Ubsan.M.loaded_segments (0xb7ec4 : word) = Some W_b6034.
Proof. vm_refl. Qed.
Lemma D_b6034 : decode_any W_b6034 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6038 : bv 32 := 0xfec6a423.
Lemma F_b6038 : fetch_word Ubsan.M.loaded_segments (0xb7ec8 : word) = Some W_b6038.
Proof. vm_refl. Qed.
Lemma D_b6038 : decode_any W_b6038 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_b603c : bv 32 := 0xfec6a623.
Lemma F_b603c : fetch_word Ubsan.M.loaded_segments (0xb7ecc : word) = Some W_b603c.
Proof. vm_refl. Qed.
Lemma D_b603c : decode_any W_b603c = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6040 : bv 32 := 0xfec6a823.
Lemma F_b6040 : fetch_word Ubsan.M.loaded_segments (0xb7ed0 : word) = Some W_b6040.
Proof. vm_refl. Qed.
Lemma D_b6040 : decode_any W_b6040 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6044 : bv 32 := 0x03076a63.
Lemma F_b6044 : fetch_word Ubsan.M.loaded_segments (0xb7ed4 : word) = Some W_b6044.
Proof. vm_refl. Qed.
Lemma D_b6044 : decode_any W_b6044 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6048 : bv 32 := 0x02061613.
Lemma F_b6048 : fetch_word Ubsan.M.loaded_segments (0xb7ed8 : word) = Some W_b6048.
Proof. vm_refl. Qed.
Lemma D_b6048 : decode_any W_b6048 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_b604c : bv 32 := 0x00f585b3.
Lemma F_b604c : fetch_word Ubsan.M.loaded_segments (0xb7edc : word) = Some W_b604c.
Proof. vm_refl. Qed.
Lemma D_b604c : decode_any W_b604c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6050 : bv 32 := 0x02065693.
Lemma F_b6050 : fetch_word Ubsan.M.loaded_segments (0xb7ee0 : word) = Some W_b6050.
Proof. vm_refl. Qed.
Lemma D_b6050 : decode_any W_b6050 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6054 : bv 32 := 0x00d66633.
Lemma F_b6054 : fetch_word Ubsan.M.loaded_segments (0xb7ee4 : word) = Some W_b6054.
Proof. vm_refl. Qed.
Lemma D_b6054 : decode_any W_b6054 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6058 : bv 32 := 0x01f00693.
Lemma F_b6058 : fetch_word Ubsan.M.loaded_segments (0xb7ee8 : word) = Some W_b6058.
Proof. vm_refl. Qed.
Lemma D_b6058 : decode_any W_b6058 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_b605c : bv 32 := 0x00c5b023.
Lemma F_b605c : fetch_word Ubsan.M.loaded_segments (0xb7eec : word) = Some W_b605c.
Proof. vm_refl. Qed.
Lemma D_b605c : decode_any W_b605c = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6060 : bv 32 := 0x00c5b423.
Lemma F_b6060 : fetch_word Ubsan.M.loaded_segments (0xb7ef0 : word) = Some W_b6060.
Proof. vm_refl. Qed.
Lemma D_b6060 : decode_any W_b6060 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6064 : bv 32 := 0x00c5b823.
Lemma F_b6064 : fetch_word Ubsan.M.loaded_segments (0xb7ef4 : word) = Some W_b6064.
Proof. vm_refl. Qed.
Lemma D_b6064 : decode_any W_b6064 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6068 : bv 32 := 0x00c5bc23.
Lemma F_b6068 : fetch_word Ubsan.M.loaded_segments (0xb7ef8 : word) = Some W_b6068.
Proof. vm_refl. Qed.
Lemma D_b6068 : decode_any W_b6068 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b606c : bv 32 := 0xfe070713.
Lemma F_b606c : fetch_word Ubsan.M.loaded_segments (0xb7efc : word) = Some W_b606c.
Proof. vm_refl. Qed.
Lemma D_b606c : decode_any W_b606c = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6070 : bv 32 := 0x02058593.
Lemma F_b6070 : fetch_word Ubsan.M.loaded_segments (0xb7f00 : word) = Some W_b6070.
Proof. vm_refl. Qed.
Lemma D_b6070 : decode_any W_b6070 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6074 : bv 32 := 0xfee6e4e3.
Lemma F_b6074 : fetch_word Ubsan.M.loaded_segments (0xb7f04 : word) = Some W_b6074.
Proof. vm_refl. Qed.
Lemma D_b6074 : decode_any W_b6074 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6078 : bv 32 := 0x00008067.
Lemma F_b6078 : fetch_word Ubsan.M.loaded_segments (0xb7f08 : word) = Some W_b6078.
Proof. vm_refl. Qed.
Lemma D_b6078 : decode_any W_b6078 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6468 : bv 32 := 0x00757593.
Lemma F_b6468 : fetch_word Ubsan.M.loaded_segments (0xb82f8 : word) = Some W_b6468.
Proof. vm_refl. Qed.
Lemma D_b6468 : decode_any W_b6468 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_b646c : bv 32 := 0x00050613.
Lemma F_b646c : fetch_word Ubsan.M.loaded_segments (0xb82fc : word) = Some W_b646c.
Proof. vm_refl. Qed.
Lemma D_b646c : decode_any W_b646c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6470 : bv 32 := 0x02058a63.
Lemma F_b6470 : fetch_word Ubsan.M.loaded_segments (0xb8300 : word) = Some W_b6470.
Proof. vm_refl. Qed.
Lemma D_b6470 : decode_any W_b6470 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6474 : bv 32 := 0x00054583.
Lemma F_b6474 : fetch_word Ubsan.M.loaded_segments (0xb8304 : word) = Some W_b6474.
Proof. vm_refl. Qed.
Lemma D_b6474 : decode_any W_b6474 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6478 : bv 32 := 0x06058c63.
Lemma F_b6478 : fetch_word Ubsan.M.loaded_segments (0xb8308 : word) = Some W_b6478.
Proof. vm_refl. Qed.
Lemma D_b6478 : decode_any W_b6478 = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_b647c : bv 32 := 0x00150613.
Lemma F_b647c : fetch_word Ubsan.M.loaded_segments (0xb830c : word) = Some W_b647c.
Proof. vm_refl. Qed.
Lemma D_b647c : decode_any W_b647c = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6480 : bv 32 := 0x00050593.
Lemma F_b6480 : fetch_word Ubsan.M.loaded_segments (0xb8310 : word) = Some W_b6480.
Proof. vm_refl. Qed.
Lemma D_b6480 : decode_any W_b6480 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6484 : bv 32 := 0x00158693.
Lemma F_b6484 : fetch_word Ubsan.M.loaded_segments (0xb8314 : word) = Some W_b6484.
Proof. vm_refl. Qed.
Lemma D_b6484 : decode_any W_b6484 = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6488 : bv 32 := 0x0076f693.
Lemma F_b6488 : fetch_word Ubsan.M.loaded_segments (0xb8318 : word) = Some W_b6488.
Proof. vm_refl. Qed.
Lemma D_b6488 : decode_any W_b6488 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_b648c : bv 32 := 0x00068c63.
Lemma F_b648c : fetch_word Ubsan.M.loaded_segments (0xb831c : word) = Some W_b648c.
Proof. vm_refl. Qed.
Lemma D_b648c : decode_any W_b648c = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6490 : bv 32 := 0x00064683.
Lemma F_b6490 : fetch_word Ubsan.M.loaded_segments (0xb8320 : word) = Some W_b6490.
Proof. vm_refl. Qed.
Lemma D_b6490 : decode_any W_b6490 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6494 : bv 32 := 0x00160613.
Lemma F_b6494 : fetch_word Ubsan.M.loaded_segments (0xb8324 : word) = Some W_b6494.
Proof. vm_refl. Qed.
Lemma D_b6494 : decode_any W_b6494 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6498 : bv 32 := 0x00158593.
Lemma F_b6498 : fetch_word Ubsan.M.loaded_segments (0xb8328 : word) = Some W_b6498.
Proof. vm_refl. Qed.
Lemma D_b6498 : decode_any W_b6498 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b649c : bv 32 := 0xfe0694e3.
Lemma F_b649c : fetch_word Ubsan.M.loaded_segments (0xb832c : word) = Some W_b649c.
Proof. vm_refl. Qed.
Lemma D_b649c : decode_any W_b649c = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64a0 : bv 32 := 0x0480006f.
Lemma F_b64a0 : fetch_word Ubsan.M.loaded_segments (0xb8330 : word) = Some W_b64a0.
Proof. vm_refl. Qed.
Lemma D_b64a0 : decode_any W_b64a0 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64a4 : bv 32 := 0xfff5c597.
Lemma F_b64a4 : fetch_word Ubsan.M.loaded_segments (0xb8334 : word) = Some W_b64a4.
Proof. vm_refl. Qed.
Lemma D_b64a4 : decode_any W_b64a4 = Some (Auipc 11 1048412, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64a8 : bv 32 := 0xfff5c717.
Lemma F_b64a8 : fetch_word Ubsan.M.loaded_segments (0xb8338 : word) = Some W_b64a8.
Proof. vm_refl. Qed.
Lemma D_b64a8 : decode_any W_b64a8 = Some (Auipc 14 1048412, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64ac : bv 32 := 0x4ac5b683.
Lemma F_b64ac : fetch_word Ubsan.M.loaded_segments (0xb833c : word) = Some W_b64ac.
Proof. vm_refl. Qed.
Lemma D_b64ac : decode_any W_b64ac = Some (Load SZ8 true 13 11 1196, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64b0 : bv 32 := 0x49873703.
Lemma F_b64b0 : fetch_word Ubsan.M.loaded_segments (0xb8340 : word) = Some W_b64b0.
Proof. vm_refl. Qed.
Lemma D_b64b0 : decode_any W_b64b0 = Some (Load SZ8 true 14 14 1176, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64b4 : bv 32 := 0xff760593.
Lemma F_b64b4 : fetch_word Ubsan.M.loaded_segments (0xb8344 : word) = Some W_b64b4.
Proof. vm_refl. Qed.
Lemma D_b64b4 : decode_any W_b64b4 = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64b8 : bv 32 := 0xff860613.
Lemma F_b64b8 : fetch_word Ubsan.M.loaded_segments (0xb8348 : word) = Some W_b64b8.
Proof. vm_refl. Qed.
Lemma D_b64b8 : decode_any W_b64b8 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64bc : bv 32 := 0x00863783.
Lemma F_b64bc : fetch_word Ubsan.M.loaded_segments (0xb834c : word) = Some W_b64bc.
Proof. vm_refl. Qed.
Lemma D_b64bc : decode_any W_b64bc = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64c0 : bv 32 := 0x00860613.
Lemma F_b64c0 : fetch_word Ubsan.M.loaded_segments (0xb8350 : word) = Some W_b64c0.
Proof. vm_refl. Qed.
Lemma D_b64c0 : decode_any W_b64c0 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64c4 : bv 32 := 0x40f68833.
Lemma F_b64c4 : fetch_word Ubsan.M.loaded_segments (0xb8354 : word) = Some W_b64c4.
Proof. vm_refl. Qed.
Lemma D_b64c4 : decode_any W_b64c4 = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64c8 : bv 32 := 0x00f867b3.
Lemma F_b64c8 : fetch_word Ubsan.M.loaded_segments (0xb8358 : word) = Some W_b64c8.
Proof. vm_refl. Qed.
Lemma D_b64c8 : decode_any W_b64c8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64cc : bv 32 := 0x00e7f7b3.
Lemma F_b64cc : fetch_word Ubsan.M.loaded_segments (0xb835c : word) = Some W_b64cc.
Proof. vm_refl. Qed.
Lemma D_b64cc : decode_any W_b64cc = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64d0 : bv 32 := 0x00858593.
Lemma F_b64d0 : fetch_word Ubsan.M.loaded_segments (0xb8360 : word) = Some W_b64d0.
Proof. vm_refl. Qed.
Lemma D_b64d0 : decode_any W_b64d0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64d4 : bv 32 := 0xfee784e3.
Lemma F_b64d4 : fetch_word Ubsan.M.loaded_segments (0xb8364 : word) = Some W_b64d4.
Proof. vm_refl. Qed.
Lemma D_b64d4 : decode_any W_b64d4 = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64d8 : bv 32 := 0x00064683.
Lemma F_b64d8 : fetch_word Ubsan.M.loaded_segments (0xb8368 : word) = Some W_b64d8.
Proof. vm_refl. Qed.
Lemma D_b64d8 : decode_any W_b64d8 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64dc : bv 32 := 0x00160613.
Lemma F_b64dc : fetch_word Ubsan.M.loaded_segments (0xb836c : word) = Some W_b64dc.
Proof. vm_refl. Qed.
Lemma D_b64dc : decode_any W_b64dc = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64e0 : bv 32 := 0x00158593.
Lemma F_b64e0 : fetch_word Ubsan.M.loaded_segments (0xb8370 : word) = Some W_b64e0.
Proof. vm_refl. Qed.
Lemma D_b64e0 : decode_any W_b64e0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64e4 : bv 32 := 0xfe069ae3.
Lemma F_b64e4 : fetch_word Ubsan.M.loaded_segments (0xb8374 : word) = Some W_b64e4.
Proof. vm_refl. Qed.
Lemma D_b64e4 : decode_any W_b64e4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64e8 : bv 32 := 0x40a58533.
Lemma F_b64e8 : fetch_word Ubsan.M.loaded_segments (0xb8378 : word) = Some W_b64e8.
Proof. vm_refl. Qed.
Lemma D_b64e8 : decode_any W_b64e8 = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64ec : bv 32 := 0x00008067.
Lemma F_b64ec : fetch_word Ubsan.M.loaded_segments (0xb837c : word) = Some W_b64ec.
Proof. vm_refl. Qed.
Lemma D_b64ec : decode_any W_b64ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64f0 : bv 32 := 0x40a50533.
Lemma F_b64f0 : fetch_word Ubsan.M.loaded_segments (0xb8380 : word) = Some W_b64f0.
Proof. vm_refl. Qed.
Lemma D_b64f0 : decode_any W_b64f0 = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64f4 : bv 32 := 0x00008067.
Lemma F_b64f4 : fetch_word Ubsan.M.loaded_segments (0xb8384 : word) = Some W_b64f4.
Proof. vm_refl. Qed.
Lemma D_b64f4 : decode_any W_b64f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64f8 : bv 32 := 0xfe010113.
Lemma F_b64f8 : fetch_word Ubsan.M.loaded_segments (0xb8388 : word) = Some W_b64f8.
Proof. vm_refl. Qed.
Lemma D_b64f8 : decode_any W_b64f8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_b64fc : bv 32 := 0x00113c23.
Lemma F_b64fc : fetch_word Ubsan.M.loaded_segments (0xb838c : word) = Some W_b64fc.
Proof. vm_refl. Qed.
Lemma D_b64fc : decode_any W_b64fc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6500 : bv 32 := 0x00813823.
Lemma F_b6500 : fetch_word Ubsan.M.loaded_segments (0xb8390 : word) = Some W_b6500.
Proof. vm_refl. Qed.
Lemma D_b6500 : decode_any W_b6500 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6504 : bv 32 := 0x00913423.
Lemma F_b6504 : fetch_word Ubsan.M.loaded_segments (0xb8394 : word) = Some W_b6504.
Proof. vm_refl. Qed.
Lemma D_b6504 : decode_any W_b6504 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6508 : bv 32 := 0x00058413.
Lemma F_b6508 : fetch_word Ubsan.M.loaded_segments (0xb8398 : word) = Some W_b6508.
Proof. vm_refl. Qed.
Lemma D_b6508 : decode_any W_b6508 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b650c : bv 32 := 0x00050493.
Lemma F_b650c : fetch_word Ubsan.M.loaded_segments (0xb839c : word) = Some W_b650c.
Proof. vm_refl. Qed.
Lemma D_b650c : decode_any W_b650c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6510 : bv 32 := 0x00000593.
Lemma F_b6510 : fetch_word Ubsan.M.loaded_segments (0xb83a0 : word) = Some W_b6510.
Proof. vm_refl. Qed.
Lemma D_b6510 : decode_any W_b6510 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6514 : bv 32 := 0x00040613.
Lemma F_b6514 : fetch_word Ubsan.M.loaded_segments (0xb83a4 : word) = Some W_b6514.
Proof. vm_refl. Qed.
Lemma D_b6514 : decode_any W_b6514 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6518 : bv 32 := 0xbf0ff0ef.
Lemma F_b6518 : fetch_word Ubsan.M.loaded_segments (0xb83a8 : word) = Some W_b6518.
Proof. vm_refl. Qed.
Lemma D_b6518 : decode_any W_b6518 = Some (Jal 1 2094064, 4%Z).
Proof. vm_refl. Qed.

Definition W_b651c : bv 32 := 0x00050463.
Lemma F_b651c : fetch_word Ubsan.M.loaded_segments (0xb83ac : word) = Some W_b651c.
Proof. vm_refl. Qed.
Lemma D_b651c : decode_any W_b651c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6520 : bv 32 := 0x40950433.
Lemma F_b6520 : fetch_word Ubsan.M.loaded_segments (0xb83b0 : word) = Some W_b6520.
Proof. vm_refl. Qed.
Lemma D_b6520 : decode_any W_b6520 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6524 : bv 32 := 0x00040513.
Lemma F_b6524 : fetch_word Ubsan.M.loaded_segments (0xb83b4 : word) = Some W_b6524.
Proof. vm_refl. Qed.
Lemma D_b6524 : decode_any W_b6524 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6528 : bv 32 := 0x01813083.
Lemma F_b6528 : fetch_word Ubsan.M.loaded_segments (0xb83b8 : word) = Some W_b6528.
Proof. vm_refl. Qed.
Lemma D_b6528 : decode_any W_b6528 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b652c : bv 32 := 0x01013403.
Lemma F_b652c : fetch_word Ubsan.M.loaded_segments (0xb83bc : word) = Some W_b652c.
Proof. vm_refl. Qed.
Lemma D_b652c : decode_any W_b652c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6530 : bv 32 := 0x00813483.
Lemma F_b6530 : fetch_word Ubsan.M.loaded_segments (0xb83c0 : word) = Some W_b6530.
Proof. vm_refl. Qed.
Lemma D_b6530 : decode_any W_b6530 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6534 : bv 32 := 0x02010113.
Lemma F_b6534 : fetch_word Ubsan.M.loaded_segments (0xb83c4 : word) = Some W_b6534.
Proof. vm_refl. Qed.
Lemma D_b6534 : decode_any W_b6534 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6538 : bv 32 := 0x00008067.
Lemma F_b6538 : fetch_word Ubsan.M.loaded_segments (0xb83c8 : word) = Some W_b6538.
Proof. vm_refl. Qed.
Lemma D_b6538 : decode_any W_b6538 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6694 : bv 32 := 0x0003e597.
Lemma F_b6694 : fetch_word Ubsan.M.loaded_segments (0xb8524 : word) = Some W_b6694.
Proof. vm_refl. Qed.
Lemma D_b6694 : decode_any W_b6694 = Some (Auipc 11 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6698 : bv 32 := 0x56f58683.
Lemma F_b6698 : fetch_word Ubsan.M.loaded_segments (0xb8528 : word) = Some W_b6698.
Proof. vm_refl. Qed.
Lemma D_b6698 : decode_any W_b6698 = Some (Load SZ1 true 13 11 1391, 4%Z).
Proof. vm_refl. Qed.

Definition W_b669c : bv 32 := 0x1e068863.
Lemma F_b669c : fetch_word Ubsan.M.loaded_segments (0xb852c : word) = Some W_b669c.
Proof. vm_refl. Qed.
Lemma D_b669c : decode_any W_b669c = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_b688c : bv 32 := 0x00008067.
Lemma F_b688c : fetch_word Ubsan.M.loaded_segments (0xb871c : word) = Some W_b688c.
Proof. vm_refl. Qed.
Lemma D_b688c : decode_any W_b688c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b691c : bv 32 := 0x00052583.
Lemma F_b691c : fetch_word Ubsan.M.loaded_segments (0xb87ac : word) = Some W_b691c.
Proof. vm_refl. Qed.
Lemma D_b691c : decode_any W_b691c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6920 : bv 32 := 0x0005c463.
Lemma F_b6920 : fetch_word Ubsan.M.loaded_segments (0xb87b0 : word) = Some W_b6920.
Proof. vm_refl. Qed.
Lemma D_b6920 : decode_any W_b6920 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b6924 : bv 32 := 0x00008067.
Lemma F_b6924 : fetch_word Ubsan.M.loaded_segments (0xb87b4 : word) = Some W_b6924.
Proof. vm_refl. Qed.
Lemma D_b6924 : decode_any W_b6924 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

