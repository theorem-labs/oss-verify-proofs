(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_d43fc : bv 32 := 0x00008067.
Lemma F_d43fc : fetch_word AsanUbsan.M.loaded_segments (0xd43fc : word) = Some W_d43fc.
Proof. vm_refl. Qed.
Lemma D_d43fc : decode_any W_d43fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4400 : bv 32 := 0xfc17b06f.
Lemma F_d4400 : fetch_word AsanUbsan.M.loaded_segments (0xd4400 : word) = Some W_d4400.
Proof. vm_refl. Qed.
Lemma D_d4400 : decode_any W_d4400 = Some (Jal 0 1556416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4404 : bv 32 := 0x0ff5f593.
Lemma F_d4404 : fetch_word AsanUbsan.M.loaded_segments (0xd4404 : word) = Some W_d4404.
Proof. vm_refl. Qed.
Lemma D_d4404 : decode_any W_d4404 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4408 : bv 32 := 0x00757693.
Lemma F_d4408 : fetch_word AsanUbsan.M.loaded_segments (0xd4408 : word) = Some W_d4408.
Proof. vm_refl. Qed.
Lemma D_d4408 : decode_any W_d4408 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d440c : bv 32 := 0x00c03733.
Lemma F_d440c : fetch_word AsanUbsan.M.loaded_segments (0xd440c : word) = Some W_d440c.
Proof. vm_refl. Qed.
Lemma D_d440c : decode_any W_d440c = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4410 : bv 32 := 0x02068c63.
Lemma F_d4410 : fetch_word AsanUbsan.M.loaded_segments (0xd4410 : word) = Some W_d4410.
Proof. vm_refl. Qed.
Lemma D_d4410 : decode_any W_d4410 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4414 : bv 32 := 0x02060a63.
Lemma F_d4414 : fetch_word AsanUbsan.M.loaded_segments (0xd4414 : word) = Some W_d4414.
Proof. vm_refl. Qed.
Lemma D_d4414 : decode_any W_d4414 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4418 : bv 32 := 0x00150793.
Lemma F_d4418 : fetch_word AsanUbsan.M.loaded_segments (0xd4418 : word) = Some W_d4418.
Proof. vm_refl. Qed.
Lemma D_d4418 : decode_any W_d4418 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d441c : bv 32 := 0x00100813.
Lemma F_d441c : fetch_word AsanUbsan.M.loaded_segments (0xd441c : word) = Some W_d441c.
Proof. vm_refl. Qed.
Lemma D_d441c : decode_any W_d441c = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4420 : bv 32 := 0x00054703.
Lemma F_d4420 : fetch_word AsanUbsan.M.loaded_segments (0xd4420 : word) = Some W_d4420.
Proof. vm_refl. Qed.
Lemma D_d4420 : decode_any W_d4420 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4424 : bv 32 := 0x00060693.
Lemma F_d4424 : fetch_word AsanUbsan.M.loaded_segments (0xd4424 : word) = Some W_d4424.
Proof. vm_refl. Qed.
Lemma D_d4424 : decode_any W_d4424 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4428 : bv 32 := 0x06b70e63.
Lemma F_d4428 : fetch_word AsanUbsan.M.loaded_segments (0xd4428 : word) = Some W_d4428.
Proof. vm_refl. Qed.
Lemma D_d4428 : decode_any W_d4428 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d442c : bv 32 := 0x00150513.
Lemma F_d442c : fetch_word AsanUbsan.M.loaded_segments (0xd442c : word) = Some W_d442c.
Proof. vm_refl. Qed.
Lemma D_d442c : decode_any W_d442c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4430 : bv 32 := 0xfff68613.
Lemma F_d4430 : fetch_word AsanUbsan.M.loaded_segments (0xd4430 : word) = Some W_d4430.
Proof. vm_refl. Qed.
Lemma D_d4430 : decode_any W_d4430 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4434 : bv 32 := 0x0077f893.
Lemma F_d4434 : fetch_word AsanUbsan.M.loaded_segments (0xd4434 : word) = Some W_d4434.
Proof. vm_refl. Qed.
Lemma D_d4434 : decode_any W_d4434 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4438 : bv 32 := 0x00c03733.
Lemma F_d4438 : fetch_word AsanUbsan.M.loaded_segments (0xd4438 : word) = Some W_d4438.
Proof. vm_refl. Qed.
Lemma D_d4438 : decode_any W_d4438 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d443c : bv 32 := 0x00088663.
Lemma F_d443c : fetch_word AsanUbsan.M.loaded_segments (0xd443c : word) = Some W_d443c.
Proof. vm_refl. Qed.
Lemma D_d443c : decode_any W_d443c = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4440 : bv 32 := 0x00178793.
Lemma F_d4440 : fetch_word AsanUbsan.M.loaded_segments (0xd4440 : word) = Some W_d4440.
Proof. vm_refl. Qed.
Lemma D_d4440 : decode_any W_d4440 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4444 : bv 32 := 0xfd069ee3.
Lemma F_d4444 : fetch_word AsanUbsan.M.loaded_segments (0xd4444 : word) = Some W_d4444.
Proof. vm_refl. Qed.
Lemma D_d4444 : decode_any W_d4444 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4448 : bv 32 := 0x06070863.
Lemma F_d4448 : fetch_word AsanUbsan.M.loaded_segments (0xd4448 : word) = Some W_d4448.
Proof. vm_refl. Qed.
Lemma D_d4448 : decode_any W_d4448 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d444c : bv 32 := 0x00054683.
Lemma F_d444c : fetch_word AsanUbsan.M.loaded_segments (0xd444c : word) = Some W_d444c.
Proof. vm_refl. Qed.
Lemma D_d444c : decode_any W_d444c = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4450 : bv 32 := 0x04b68663.
Lemma F_d4450 : fetch_word AsanUbsan.M.loaded_segments (0xd4450 : word) = Some W_d4450.
Proof. vm_refl. Qed.
Lemma D_d4450 : decode_any W_d4450 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4454 : bv 32 := 0x00800693.
Lemma F_d4454 : fetch_word AsanUbsan.M.loaded_segments (0xd4454 : word) = Some W_d4454.
Proof. vm_refl. Qed.
Lemma D_d4454 : decode_any W_d4454 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4458 : bv 32 := 0x04d66263.
Lemma F_d4458 : fetch_word AsanUbsan.M.loaded_segments (0xd4458 : word) = Some W_d4458.
Proof. vm_refl. Qed.
Lemma D_d4458 : decode_any W_d4458 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d445c : bv 32 := 0xfff3c697.
Lemma F_d445c : fetch_word AsanUbsan.M.loaded_segments (0xd445c : word) = Some W_d445c.
Proof. vm_refl. Qed.
Lemma D_d445c : decode_any W_d445c = Some (Auipc 13 1048380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4460 : bv 32 := 0xf6c6b683.
Lemma F_d4460 : fetch_word AsanUbsan.M.loaded_segments (0xd4460 : word) = Some W_d4460.
Proof. vm_refl. Qed.
Lemma D_d4460 : decode_any W_d4460 = Some (Load SZ8 true 13 13 3948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4464 : bv 32 := 0xfff3c717.
Lemma F_d4464 : fetch_word AsanUbsan.M.loaded_segments (0xd4464 : word) = Some W_d4464.
Proof. vm_refl. Qed.
Lemma D_d4464 : decode_any W_d4464 = Some (Auipc 14 1048380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4468 : bv 32 := 0xf4473703.
Lemma F_d4468 : fetch_word AsanUbsan.M.loaded_segments (0xd4468 : word) = Some W_d4468.
Proof. vm_refl. Qed.
Lemma D_d4468 : decode_any W_d4468 = Some (Load SZ8 true 14 14 3908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d446c : bv 32 := 0x00168793.
Lemma F_d446c : fetch_word AsanUbsan.M.loaded_segments (0xd446c : word) = Some W_d446c.
Proof. vm_refl. Qed.
Lemma D_d446c : decode_any W_d446c = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4470 : bv 32 := 0x02f587b3.
Lemma F_d4470 : fetch_word AsanUbsan.M.loaded_segments (0xd4470 : word) = Some W_d4470.
Proof. vm_refl. Qed.
Lemma D_d4470 : decode_any W_d4470 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4474 : bv 32 := 0x00700813.
Lemma F_d4474 : fetch_word AsanUbsan.M.loaded_segments (0xd4474 : word) = Some W_d4474.
Proof. vm_refl. Qed.
Lemma D_d4474 : decode_any W_d4474 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4478 : bv 32 := 0x00053883.
Lemma F_d4478 : fetch_word AsanUbsan.M.loaded_segments (0xd4478 : word) = Some W_d4478.
Proof. vm_refl. Qed.
Lemma D_d4478 : decode_any W_d4478 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d447c : bv 32 := 0x00f8c8b3.
Lemma F_d447c : fetch_word AsanUbsan.M.loaded_segments (0xd447c : word) = Some W_d447c.
Proof. vm_refl. Qed.
Lemma D_d447c : decode_any W_d447c = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4480 : bv 32 := 0x411682b3.
Lemma F_d4480 : fetch_word AsanUbsan.M.loaded_segments (0xd4480 : word) = Some W_d4480.
Proof. vm_refl. Qed.
Lemma D_d4480 : decode_any W_d4480 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4484 : bv 32 := 0x0112e8b3.
Lemma F_d4484 : fetch_word AsanUbsan.M.loaded_segments (0xd4484 : word) = Some W_d4484.
Proof. vm_refl. Qed.
Lemma D_d4484 : decode_any W_d4484 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4488 : bv 32 := 0x00e8f8b3.
Lemma F_d4488 : fetch_word AsanUbsan.M.loaded_segments (0xd4488 : word) = Some W_d4488.
Proof. vm_refl. Qed.
Lemma D_d4488 : decode_any W_d4488 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d448c : bv 32 := 0x02e89a63.
Lemma F_d448c : fetch_word AsanUbsan.M.loaded_segments (0xd448c : word) = Some W_d448c.
Proof. vm_refl. Qed.
Lemma D_d448c : decode_any W_d448c = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4490 : bv 32 := 0xff860613.
Lemma F_d4490 : fetch_word AsanUbsan.M.loaded_segments (0xd4490 : word) = Some W_d4490.
Proof. vm_refl. Qed.
Lemma D_d4490 : decode_any W_d4490 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4494 : bv 32 := 0x00850513.
Lemma F_d4494 : fetch_word AsanUbsan.M.loaded_segments (0xd4494 : word) = Some W_d4494.
Proof. vm_refl. Qed.
Lemma D_d4494 : decode_any W_d4494 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4498 : bv 32 := 0xfec860e3.
Lemma F_d4498 : fetch_word AsanUbsan.M.loaded_segments (0xd4498 : word) = Some W_d4498.
Proof. vm_refl. Qed.
Lemma D_d4498 : decode_any W_d4498 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d449c : bv 32 := 0x00060693.
Lemma F_d449c : fetch_word AsanUbsan.M.loaded_segments (0xd449c : word) = Some W_d449c.
Proof. vm_refl. Qed.
Lemma D_d449c : decode_any W_d449c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44a0 : bv 32 := 0x00060c63.
Lemma F_d44a0 : fetch_word AsanUbsan.M.loaded_segments (0xd44a0 : word) = Some W_d44a0.
Proof. vm_refl. Qed.
Lemma D_d44a0 : decode_any W_d44a0 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44a4 : bv 32 := 0x00054603.
Lemma F_d44a4 : fetch_word AsanUbsan.M.loaded_segments (0xd44a4 : word) = Some W_d44a4.
Proof. vm_refl. Qed.
Lemma D_d44a4 : decode_any W_d44a4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44a8 : bv 32 := 0x00b60a63.
Lemma F_d44a8 : fetch_word AsanUbsan.M.loaded_segments (0xd44a8 : word) = Some W_d44a8.
Proof. vm_refl. Qed.
Lemma D_d44a8 : decode_any W_d44a8 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44ac : bv 32 := 0xfff68693.
Lemma F_d44ac : fetch_word AsanUbsan.M.loaded_segments (0xd44ac : word) = Some W_d44ac.
Proof. vm_refl. Qed.
Lemma D_d44ac : decode_any W_d44ac = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44b0 : bv 32 := 0x00150513.
Lemma F_d44b0 : fetch_word AsanUbsan.M.loaded_segments (0xd44b0 : word) = Some W_d44b0.
Proof. vm_refl. Qed.
Lemma D_d44b0 : decode_any W_d44b0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44b4 : bv 32 := 0xfe0698e3.
Lemma F_d44b4 : fetch_word AsanUbsan.M.loaded_segments (0xd44b4 : word) = Some W_d44b4.
Proof. vm_refl. Qed.
Lemma D_d44b4 : decode_any W_d44b4 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44b8 : bv 32 := 0x00000513.
Lemma F_d44b8 : fetch_word AsanUbsan.M.loaded_segments (0xd44b8 : word) = Some W_d44b8.
Proof. vm_refl. Qed.
Lemma D_d44b8 : decode_any W_d44b8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44bc : bv 32 := 0x00008067.
Lemma F_d44bc : fetch_word AsanUbsan.M.loaded_segments (0xd44bc : word) = Some W_d44bc.
Proof. vm_refl. Qed.
Lemma D_d44bc : decode_any W_d44bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44c0 : bv 32 := 0x00060693.
Lemma F_d44c0 : fetch_word AsanUbsan.M.loaded_segments (0xd44c0 : word) = Some W_d44c0.
Proof. vm_refl. Qed.
Lemma D_d44c0 : decode_any W_d44c0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44c4 : bv 32 := 0x00054603.
Lemma F_d44c4 : fetch_word AsanUbsan.M.loaded_segments (0xd44c4 : word) = Some W_d44c4.
Proof. vm_refl. Qed.
Lemma D_d44c4 : decode_any W_d44c4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44c8 : bv 32 := 0xfeb612e3.
Lemma F_d44c8 : fetch_word AsanUbsan.M.loaded_segments (0xd44c8 : word) = Some W_d44c8.
Proof. vm_refl. Qed.
Lemma D_d44c8 : decode_any W_d44c8 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44cc : bv 32 := 0xff1ff06f.
Lemma F_d44cc : fetch_word AsanUbsan.M.loaded_segments (0xd44cc : word) = Some W_d44cc.
Proof. vm_refl. Qed.
Lemma D_d44cc : decode_any W_d44cc = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44d0 : bv 32 := 0x02060063.
Lemma F_d44d0 : fetch_word AsanUbsan.M.loaded_segments (0xd44d0 : word) = Some W_d44d0.
Proof. vm_refl. Qed.
Lemma D_d44d0 : decode_any W_d44d0 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44d4 : bv 32 := 0x00054683.
Lemma F_d44d4 : fetch_word AsanUbsan.M.loaded_segments (0xd44d4 : word) = Some W_d44d4.
Proof. vm_refl. Qed.
Lemma D_d44d4 : decode_any W_d44d4 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44d8 : bv 32 := 0x0005c703.
Lemma F_d44d8 : fetch_word AsanUbsan.M.loaded_segments (0xd44d8 : word) = Some W_d44d8.
Proof. vm_refl. Qed.
Lemma D_d44d8 : decode_any W_d44d8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44dc : bv 32 := 0x00e69e63.
Lemma F_d44dc : fetch_word AsanUbsan.M.loaded_segments (0xd44dc : word) = Some W_d44dc.
Proof. vm_refl. Qed.
Lemma D_d44dc : decode_any W_d44dc = Some (Branch BC_NE 13 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44e0 : bv 32 := 0xfff60613.
Lemma F_d44e0 : fetch_word AsanUbsan.M.loaded_segments (0xd44e0 : word) = Some W_d44e0.
Proof. vm_refl. Qed.
Lemma D_d44e0 : decode_any W_d44e0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44e4 : bv 32 := 0x00150513.
Lemma F_d44e4 : fetch_word AsanUbsan.M.loaded_segments (0xd44e4 : word) = Some W_d44e4.
Proof. vm_refl. Qed.
Lemma D_d44e4 : decode_any W_d44e4 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44e8 : bv 32 := 0x00158593.
Lemma F_d44e8 : fetch_word AsanUbsan.M.loaded_segments (0xd44e8 : word) = Some W_d44e8.
Proof. vm_refl. Qed.
Lemma D_d44e8 : decode_any W_d44e8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44ec : bv 32 := 0xfe0614e3.
Lemma F_d44ec : fetch_word AsanUbsan.M.loaded_segments (0xd44ec : word) = Some W_d44ec.
Proof. vm_refl. Qed.
Lemma D_d44ec : decode_any W_d44ec = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44f0 : bv 32 := 0x00000513.
Lemma F_d44f0 : fetch_word AsanUbsan.M.loaded_segments (0xd44f0 : word) = Some W_d44f0.
Proof. vm_refl. Qed.
Lemma D_d44f0 : decode_any W_d44f0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44f4 : bv 32 := 0x00008067.
Lemma F_d44f4 : fetch_word AsanUbsan.M.loaded_segments (0xd44f4 : word) = Some W_d44f4.
Proof. vm_refl. Qed.
Lemma D_d44f4 : decode_any W_d44f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d44f8 : bv 32 := 0x40e68533.
Lemma F_d44f8 : fetch_word AsanUbsan.M.loaded_segments (0xd44f8 : word) = Some W_d44f8.
Proof. vm_refl. Qed.
Lemma D_d44f8 : decode_any W_d44f8 = Some (Op ALU_SUB 10 13 14, 4%Z).
Proof. vm_refl. Qed.
