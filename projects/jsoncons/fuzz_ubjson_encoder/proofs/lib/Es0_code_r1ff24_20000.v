(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_343a0 : bv 32 := 0xfffdc197.
Lemma F_343a0 : fetch_word Plain.M.loaded_segments (0x343f8 : word) = Some W_343a0.
Proof. vm_refl. Qed.
Lemma D_343a0 : decode_any W_343a0 = Some (Auipc 3 1048540, 4%Z).
Proof. vm_refl. Qed.

Definition W_343a4 : bv 32 := 0x40818193.
Lemma F_343a4 : fetch_word Plain.M.loaded_segments (0x343fc : word) = Some W_343a4.
Proof. vm_refl. Qed.
Lemma D_343a4 : decode_any W_343a4 = Some (OpImm ALU_ADD 3 3 1032, 4%Z).
Proof. vm_refl. Qed.

Definition W_343a8 : bv 32 := 0x00010513.
Lemma F_343a8 : fetch_word Plain.M.loaded_segments (0x34400 : word) = Some W_343a8.
Proof. vm_refl. Qed.
Lemma D_343a8 : decode_any W_343a8 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_343ac : bv 32 := 0xfffcc597.
Lemma F_343ac : fetch_word Plain.M.loaded_segments (0x34404 : word) = Some W_343ac.
Proof. vm_refl. Qed.
Lemma D_343ac : decode_any W_343ac = Some (Auipc 11 1048524, 4%Z).
Proof. vm_refl. Qed.

Definition W_343b0 : bv 32 := 0xbfc58593.
Lemma F_343b0 : fetch_word Plain.M.loaded_segments (0x34408 : word) = Some W_343b0.
Proof. vm_refl. Qed.
Lemma D_343b0 : decode_any W_343b0 = Some (OpImm ALU_ADD 11 11 3068, 4%Z).
Proof. vm_refl. Qed.

Definition W_343b4 : bv 32 := 0xff017113.
Lemma F_343b4 : fetch_word Plain.M.loaded_segments (0x3440c : word) = Some W_343b4.
Proof. vm_refl. Qed.
Lemma D_343b4 : decode_any W_343b4 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_343b8 : bv 32 := 0x0040006f.
Lemma F_343b8 : fetch_word Plain.M.loaded_segments (0x34410 : word) = Some W_343b8.
Proof. vm_refl. Qed.
Lemma D_343b8 : decode_any W_343b8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_343bc : bv 32 := 0x00052583.
Lemma F_343bc : fetch_word Plain.M.loaded_segments (0x34414 : word) = Some W_343bc.
Proof. vm_refl. Qed.
Lemma D_343bc : decode_any W_343bc = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_343c0 : bv 32 := 0x00084617.
Lemma F_343c0 : fetch_word Plain.M.loaded_segments (0x34418 : word) = Some W_343c0.
Proof. vm_refl. Qed.
Lemma D_343c0 : decode_any W_343c0 = Some (Auipc 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_343c4 : bv 32 := 0x00084697.
Lemma F_343c4 : fetch_word Plain.M.loaded_segments (0x3441c : word) = Some W_343c4.
Proof. vm_refl. Qed.
Lemma D_343c4 : decode_any W_343c4 = Some (Auipc 13 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_343c8 : bv 32 := 0x00084717.
Lemma F_343c8 : fetch_word Plain.M.loaded_segments (0x34420 : word) = Some W_343c8.
Proof. vm_refl. Qed.
Lemma D_343c8 : decode_any W_343c8 = Some (Auipc 14 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_343cc : bv 32 := 0xd0063783.
Lemma F_343cc : fetch_word Plain.M.loaded_segments (0x34424 : word) = Some W_343cc.
Proof. vm_refl. Qed.
Lemma D_343cc : decode_any W_343cc = Some (Load SZ8 true 15 12 3328, 4%Z).
Proof. vm_refl. Qed.

Definition W_343d0 : bv 32 := 0xd046b683.
Lemma F_343d0 : fetch_word Plain.M.loaded_segments (0x34428 : word) = Some W_343d0.
Proof. vm_refl. Qed.
Lemma D_343d0 : decode_any W_343d0 = Some (Load SZ8 true 13 13 3332, 4%Z).
Proof. vm_refl. Qed.

Definition W_343d4 : bv 32 := 0xd0873703.
Lemma F_343d4 : fetch_word Plain.M.loaded_segments (0x3442c : word) = Some W_343d4.
Proof. vm_refl. Qed.
Lemma D_343d4 : decode_any W_343d4 = Some (Load SZ8 true 14 14 3336, 4%Z).
Proof. vm_refl. Qed.

Definition W_343d8 : bv 32 := 0x00850613.
Lemma F_343d8 : fetch_word Plain.M.loaded_segments (0x34430 : word) = Some W_343d8.
Proof. vm_refl. Qed.
Lemma D_343d8 : decode_any W_343d8 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_343dc : bv 32 := 0x00078513.
Lemma F_343dc : fetch_word Plain.M.loaded_segments (0x34434 : word) = Some W_343dc.
Proof. vm_refl. Qed.
Lemma D_343dc : decode_any W_343dc = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_343e0 : bv 32 := 0x00000793.
Lemma F_343e0 : fetch_word Plain.M.loaded_segments (0x34438 : word) = Some W_343e0.
Proof. vm_refl. Qed.
Lemma D_343e0 : decode_any W_343e0 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_343e4 : bv 32 := 0x2cc6706f.
Lemma F_343e4 : fetch_word Plain.M.loaded_segments (0x3443c : word) = Some W_343e4.
Proof. vm_refl. Qed.
Lemma D_343e4 : decode_any W_343e4 = Some (Jal 0 422604, 4%Z).
Proof. vm_refl. Qed.

Definition W_343e8 : bv 32 := 0xff010113.
Lemma F_343e8 : fetch_word Plain.M.loaded_segments (0x34440 : word) = Some W_343e8.
Proof. vm_refl. Qed.
Lemma D_343e8 : decode_any W_343e8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_343ec : bv 32 := 0x00113423.
Lemma F_343ec : fetch_word Plain.M.loaded_segments (0x34444 : word) = Some W_343ec.
Proof. vm_refl. Qed.
Lemma D_343ec : decode_any W_343ec = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_343f0 : bv 32 := 0x00813023.
Lemma F_343f0 : fetch_word Plain.M.loaded_segments (0x34448 : word) = Some W_343f0.
Proof. vm_refl. Qed.
Lemma D_343f0 : decode_any W_343f0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_343f4 : bv 32 := 0x01010413.
Lemma F_343f4 : fetch_word Plain.M.loaded_segments (0x3444c : word) = Some W_343f4.
Proof. vm_refl. Qed.
Lemma D_343f4 : decode_any W_343f4 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_343f8 : bv 32 := 0x00085517.
Lemma F_343f8 : fetch_word Plain.M.loaded_segments (0x34450 : word) = Some W_343f8.
Proof. vm_refl. Qed.
Lemma D_343f8 : decode_any W_343f8 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_343fc : bv 32 := 0x17050513.
Lemma F_343fc : fetch_word Plain.M.loaded_segments (0x34454 : word) = Some W_343fc.
Proof. vm_refl. Qed.
Lemma D_343fc : decode_any W_343fc = Some (OpImm ALU_ADD 10 10 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_34400 : bv 32 := 0x00054503.
Lemma F_34400 : fetch_word Plain.M.loaded_segments (0x34458 : word) = Some W_34400.
Proof. vm_refl. Qed.
Lemma D_34400 : decode_any W_34400 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34404 : bv 32 := 0x00157513.
Lemma F_34404 : fetch_word Plain.M.loaded_segments (0x3445c : word) = Some W_34404.
Proof. vm_refl. Qed.
Lemma D_34404 : decode_any W_34404 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_34408 : bv 32 := 0x00050663.
Lemma F_34408 : fetch_word Plain.M.loaded_segments (0x34460 : word) = Some W_34408.
Proof. vm_refl. Qed.
Lemma D_34408 : decode_any W_34408 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_34414 : bv 32 := 0x00085517.
Lemma F_34414 : fetch_word Plain.M.loaded_segments (0x3446c : word) = Some W_34414.
Proof. vm_refl. Qed.
Lemma D_34414 : decode_any W_34414 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_34418 : bv 32 := 0x15450593.
Lemma F_34418 : fetch_word Plain.M.loaded_segments (0x34470 : word) = Some W_34418.
Proof. vm_refl. Qed.
Lemma D_34418 : decode_any W_34418 = Some (OpImm ALU_ADD 11 10 340, 4%Z).
Proof. vm_refl. Qed.

Definition W_3441c : bv 32 := 0x00100513.
Lemma F_3441c : fetch_word Plain.M.loaded_segments (0x34474 : word) = Some W_3441c.
Proof. vm_refl. Qed.
Lemma D_3441c : decode_any W_3441c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_34420 : bv 32 := 0x00a58023.
Lemma F_34420 : fetch_word Plain.M.loaded_segments (0x34478 : word) = Some W_34420.
Proof. vm_refl. Qed.
Lemma D_34420 : decode_any W_34420 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34424 : bv 32 := 0x00084517.
Lemma F_34424 : fetch_word Plain.M.loaded_segments (0x3447c : word) = Some W_34424.
Proof. vm_refl. Qed.
Lemma D_34424 : decode_any W_34424 = Some (Auipc 10 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_34428 : bv 32 := 0xcb453503.
Lemma F_34428 : fetch_word Plain.M.loaded_segments (0x34480 : word) = Some W_34428.
Proof. vm_refl. Qed.
Lemma D_34428 : decode_any W_34428 = Some (Load SZ8 true 10 10 3252, 4%Z).
Proof. vm_refl. Qed.

Definition W_3442c : bv 32 := 0x02050063.
Lemma F_3442c : fetch_word Plain.M.loaded_segments (0x34484 : word) = Some W_3442c.
Proof. vm_refl. Qed.
Lemma D_3442c : decode_any W_3442c = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3444c : bv 32 := 0x00813083.
Lemma F_3444c : fetch_word Plain.M.loaded_segments (0x344a4 : word) = Some W_3444c.
Proof. vm_refl. Qed.
Lemma D_3444c : decode_any W_3444c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_34450 : bv 32 := 0x00013403.
Lemma F_34450 : fetch_word Plain.M.loaded_segments (0x344a8 : word) = Some W_34450.
Proof. vm_refl. Qed.
Lemma D_34450 : decode_any W_34450 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34454 : bv 32 := 0x01010113.
Lemma F_34454 : fetch_word Plain.M.loaded_segments (0x344ac : word) = Some W_34454.
Proof. vm_refl. Qed.
Lemma D_34454 : decode_any W_34454 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_34458 : bv 32 := 0x00008067.
Lemma F_34458 : fetch_word Plain.M.loaded_segments (0x344b0 : word) = Some W_34458.
Proof. vm_refl. Qed.
Lemma D_34458 : decode_any W_34458 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3445c : bv 32 := 0xff010113.
Lemma F_3445c : fetch_word Plain.M.loaded_segments (0x344b4 : word) = Some W_3445c.
Proof. vm_refl. Qed.
Lemma D_3445c : decode_any W_3445c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_34460 : bv 32 := 0x00113423.
Lemma F_34460 : fetch_word Plain.M.loaded_segments (0x344b8 : word) = Some W_34460.
Proof. vm_refl. Qed.
Lemma D_34460 : decode_any W_34460 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_34464 : bv 32 := 0x00813023.
Lemma F_34464 : fetch_word Plain.M.loaded_segments (0x344bc : word) = Some W_34464.
Proof. vm_refl. Qed.
Lemma D_34464 : decode_any W_34464 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34468 : bv 32 := 0x01010413.
Lemma F_34468 : fetch_word Plain.M.loaded_segments (0x344c0 : word) = Some W_34468.
Proof. vm_refl. Qed.
Lemma D_34468 : decode_any W_34468 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3446c : bv 32 := 0x00085517.
Lemma F_3446c : fetch_word Plain.M.loaded_segments (0x344c4 : word) = Some W_3446c.
Proof. vm_refl. Qed.
Lemma D_3446c : decode_any W_3446c = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_34470 : bv 32 := 0x14450513.
Lemma F_34470 : fetch_word Plain.M.loaded_segments (0x344c8 : word) = Some W_34470.
Proof. vm_refl. Qed.
Lemma D_34470 : decode_any W_34470 = Some (OpImm ALU_ADD 10 10 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_34474 : bv 32 := 0x00054503.
Lemma F_34474 : fetch_word Plain.M.loaded_segments (0x344cc : word) = Some W_34474.
Proof. vm_refl. Qed.
Lemma D_34474 : decode_any W_34474 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34478 : bv 32 := 0x00157513.
Lemma F_34478 : fetch_word Plain.M.loaded_segments (0x344d0 : word) = Some W_34478.
Proof. vm_refl. Qed.
Lemma D_34478 : decode_any W_34478 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.
