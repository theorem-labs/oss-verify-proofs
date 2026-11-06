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

Definition W_7a67c : bv 32 := 0xfe010113.
Lemma F_7a67c : fetch_word AsanUbsan.M.loaded_segments (0x7a6cc : word) = Some W_7a67c.
Proof. vm_refl. Qed.
Lemma D_7a67c : decode_any W_7a67c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a680 : bv 32 := 0x00113c23.
Lemma F_7a680 : fetch_word AsanUbsan.M.loaded_segments (0x7a6d0 : word) = Some W_7a680.
Proof. vm_refl. Qed.
Lemma D_7a680 : decode_any W_7a680 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a684 : bv 32 := 0x00813823.
Lemma F_7a684 : fetch_word AsanUbsan.M.loaded_segments (0x7a6d4 : word) = Some W_7a684.
Proof. vm_refl. Qed.
Lemma D_7a684 : decode_any W_7a684 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a688 : bv 32 := 0x00913423.
Lemma F_7a688 : fetch_word AsanUbsan.M.loaded_segments (0x7a6d8 : word) = Some W_7a688.
Proof. vm_refl. Qed.
Lemma D_7a688 : decode_any W_7a688 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a68c : bv 32 := 0x01213023.
Lemma F_7a68c : fetch_word AsanUbsan.M.loaded_segments (0x7a6dc : word) = Some W_7a68c.
Proof. vm_refl. Qed.
Lemma D_7a68c : decode_any W_7a68c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a690 : bv 32 := 0x00058413.
Lemma F_7a690 : fetch_word AsanUbsan.M.loaded_segments (0x7a6e0 : word) = Some W_7a690.
Proof. vm_refl. Qed.
Lemma D_7a690 : decode_any W_7a690 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a694 : bv 32 := 0x00050493.
Lemma F_7a694 : fetch_word AsanUbsan.M.loaded_segments (0x7a6e4 : word) = Some W_7a694.
Proof. vm_refl. Qed.
Lemma D_7a694 : decode_any W_7a694 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a698 : bv 32 := 0x030000ef.
Lemma F_7a698 : fetch_word AsanUbsan.M.loaded_segments (0x7a6e8 : word) = Some W_7a698.
Proof. vm_refl. Qed.
Lemma D_7a698 : decode_any W_7a698 = Some (Jal 1 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a69c : bv 32 := 0x00050913.
Lemma F_7a69c : fetch_word AsanUbsan.M.loaded_segments (0x7a6ec : word) = Some W_7a69c.
Proof. vm_refl. Qed.
Lemma D_7a69c : decode_any W_7a69c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6a0 : bv 32 := 0x00940533.
Lemma F_7a6a0 : fetch_word AsanUbsan.M.loaded_segments (0x7a6f0 : word) = Some W_7a6a0.
Proof. vm_refl. Qed.
Lemma D_7a6a0 : decode_any W_7a6a0 = Some (Op ALU_ADD 10 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6a4 : bv 32 := 0x024000ef.
Lemma F_7a6a4 : fetch_word AsanUbsan.M.loaded_segments (0x7a6f4 : word) = Some W_7a6a4.
Proof. vm_refl. Qed.
Lemma D_7a6a4 : decode_any W_7a6a4 = Some (Jal 1 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6a8 : bv 32 := 0x00050593.
Lemma F_7a6a8 : fetch_word AsanUbsan.M.loaded_segments (0x7a6f8 : word) = Some W_7a6a8.
Proof. vm_refl. Qed.
Lemma D_7a6a8 : decode_any W_7a6a8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6ac : bv 32 := 0x00090513.
Lemma F_7a6ac : fetch_word AsanUbsan.M.loaded_segments (0x7a6fc : word) = Some W_7a6ac.
Proof. vm_refl. Qed.
Lemma D_7a6ac : decode_any W_7a6ac = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6b0 : bv 32 := 0x01813083.
Lemma F_7a6b0 : fetch_word AsanUbsan.M.loaded_segments (0x7a700 : word) = Some W_7a6b0.
Proof. vm_refl. Qed.
Lemma D_7a6b0 : decode_any W_7a6b0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6b4 : bv 32 := 0x01013403.
Lemma F_7a6b4 : fetch_word AsanUbsan.M.loaded_segments (0x7a704 : word) = Some W_7a6b4.
Proof. vm_refl. Qed.
Lemma D_7a6b4 : decode_any W_7a6b4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6b8 : bv 32 := 0x00813483.
Lemma F_7a6b8 : fetch_word AsanUbsan.M.loaded_segments (0x7a708 : word) = Some W_7a6b8.
Proof. vm_refl. Qed.
Lemma D_7a6b8 : decode_any W_7a6b8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6bc : bv 32 := 0x00013903.
Lemma F_7a6bc : fetch_word AsanUbsan.M.loaded_segments (0x7a70c : word) = Some W_7a6bc.
Proof. vm_refl. Qed.
Lemma D_7a6bc : decode_any W_7a6bc = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6c0 : bv 32 := 0x02010113.
Lemma F_7a6c0 : fetch_word AsanUbsan.M.loaded_segments (0x7a710 : word) = Some W_7a6c0.
Proof. vm_refl. Qed.
Lemma D_7a6c0 : decode_any W_7a6c0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6c4 : bv 32 := 0x3151b06f.
Lemma F_7a6c4 : fetch_word AsanUbsan.M.loaded_segments (0x7a714 : word) = Some W_7a6c4.
Proof. vm_refl. Qed.
Lemma D_7a6c4 : decode_any W_7a6c4 = Some (Jal 0 113428, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6c8 : bv 32 := 0x000c3597.
Lemma F_7a6c8 : fetch_word AsanUbsan.M.loaded_segments (0x7a718 : word) = Some W_7a6c8.
Proof. vm_refl. Qed.
Lemma D_7a6c8 : decode_any W_7a6c8 = Some (Auipc 11 195, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6cc : bv 32 := 0x1b05b583.
Lemma F_7a6cc : fetch_word AsanUbsan.M.loaded_segments (0x7a71c : word) = Some W_7a6cc.
Proof. vm_refl. Qed.
Lemma D_7a6cc : decode_any W_7a6cc = Some (Load SZ8 true 11 11 432, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6d0 : bv 32 := 0x0005b583.
Lemma F_7a6d0 : fetch_word AsanUbsan.M.loaded_segments (0x7a720 : word) = Some W_7a6d0.
Proof. vm_refl. Qed.
Lemma D_7a6d0 : decode_any W_7a6d0 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6d4 : bv 32 := 0xfff58613.
Lemma F_7a6d4 : fetch_word AsanUbsan.M.loaded_segments (0x7a724 : word) = Some W_7a6d4.
Proof. vm_refl. Qed.
Lemma D_7a6d4 : decode_any W_7a6d4 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6d8 : bv 32 := 0x00c5b6b3.
Lemma F_7a6d8 : fetch_word AsanUbsan.M.loaded_segments (0x7a728 : word) = Some W_7a6d8.
Proof. vm_refl. Qed.
Lemma D_7a6d8 : decode_any W_7a6d8 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6dc : bv 32 := 0xfff68693.
Lemma F_7a6dc : fetch_word AsanUbsan.M.loaded_segments (0x7a72c : word) = Some W_7a6dc.
Proof. vm_refl. Qed.
Lemma D_7a6dc : decode_any W_7a6dc = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6e0 : bv 32 := 0x00c6f6b3.
Lemma F_7a6e0 : fetch_word AsanUbsan.M.loaded_segments (0x7a730 : word) = Some W_7a6e0.
Proof. vm_refl. Qed.
Lemma D_7a6e0 : decode_any W_7a6e0 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6e4 : bv 32 := 0x04a6f263.
Lemma F_7a6e4 : fetch_word AsanUbsan.M.loaded_segments (0x7a734 : word) = Some W_7a6e4.
Proof. vm_refl. Qed.
Lemma D_7a6e4 : decode_any W_7a6e4 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6e8 : bv 32 := 0x000c3697.
Lemma F_7a6e8 : fetch_word AsanUbsan.M.loaded_segments (0x7a738 : word) = Some W_7a6e8.
Proof. vm_refl. Qed.
Lemma D_7a6e8 : decode_any W_7a6e8 = Some (Auipc 13 195, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6ec : bv 32 := 0x1986b683.
Lemma F_7a6ec : fetch_word AsanUbsan.M.loaded_segments (0x7a73c : word) = Some W_7a6ec.
Proof. vm_refl. Qed.
Lemma D_7a6ec : decode_any W_7a6ec = Some (Load SZ8 true 13 13 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6f0 : bv 32 := 0x000c3717.
Lemma F_7a6f0 : fetch_word AsanUbsan.M.loaded_segments (0x7a740 : word) = Some W_7a6f0.
Proof. vm_refl. Qed.
Lemma D_7a6f0 : decode_any W_7a6f0 = Some (Auipc 14 195, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6f4 : bv 32 := 0x19873703.
Lemma F_7a6f4 : fetch_word AsanUbsan.M.loaded_segments (0x7a744 : word) = Some W_7a6f4.
Proof. vm_refl. Qed.
Lemma D_7a6f4 : decode_any W_7a6f4 = Some (Load SZ8 true 14 14 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6f8 : bv 32 := 0x0006b803.
Lemma F_7a6f8 : fetch_word AsanUbsan.M.loaded_segments (0x7a748 : word) = Some W_7a6f8.
Proof. vm_refl. Qed.
Lemma D_7a6f8 : decode_any W_7a6f8 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a6fc : bv 32 := 0x00073683.
Lemma F_7a6fc : fetch_word AsanUbsan.M.loaded_segments (0x7a74c : word) = Some W_7a6fc.
Proof. vm_refl. Qed.
Lemma D_7a6fc : decode_any W_7a6fc = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a700 : bv 32 := 0xfff80793.
Lemma F_7a700 : fetch_word AsanUbsan.M.loaded_segments (0x7a750 : word) = Some W_7a700.
Proof. vm_refl. Qed.
Lemma D_7a700 : decode_any W_7a700 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a704 : bv 32 := 0x00a7f463.
Lemma F_7a704 : fetch_word AsanUbsan.M.loaded_segments (0x7a754 : word) = Some W_7a704.
Proof. vm_refl. Qed.
Lemma D_7a704 : decode_any W_7a704 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a70c : bv 32 := 0x000c3717.
Lemma F_7a70c : fetch_word AsanUbsan.M.loaded_segments (0x7a75c : word) = Some W_7a70c.
Proof. vm_refl. Qed.
Lemma D_7a70c : decode_any W_7a70c = Some (Auipc 14 195, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a710 : bv 32 := 0x18473703.
Lemma F_7a710 : fetch_word AsanUbsan.M.loaded_segments (0x7a760 : word) = Some W_7a710.
Proof. vm_refl. Qed.
Lemma D_7a710 : decode_any W_7a710 = Some (Load SZ8 true 14 14 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a714 : bv 32 := 0x00073283.
Lemma F_7a714 : fetch_word AsanUbsan.M.loaded_segments (0x7a764 : word) = Some W_7a714.
Proof. vm_refl. Qed.
Lemma D_7a714 : decode_any W_7a714 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a718 : bv 32 := 0x0032d713.
Lemma F_7a718 : fetch_word AsanUbsan.M.loaded_segments (0x7a768 : word) = Some W_7a718.
Proof. vm_refl. Qed.
Lemma D_7a718 : decode_any W_7a718 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a71c : bv 32 := 0x00b708b3.
Lemma F_7a71c : fetch_word AsanUbsan.M.loaded_segments (0x7a76c : word) = Some W_7a71c.
Proof. vm_refl. Qed.
Lemma D_7a71c : decode_any W_7a71c = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a720 : bv 32 := 0x00a2ea63.
Lemma F_7a720 : fetch_word AsanUbsan.M.loaded_segments (0x7a770 : word) = Some W_7a720.
Proof. vm_refl. Qed.
Lemma D_7a720 : decode_any W_7a720 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a724 : bv 32 := 0x00a8f863.
Lemma F_7a724 : fetch_word AsanUbsan.M.loaded_segments (0x7a774 : word) = Some W_7a724.
Proof. vm_refl. Qed.
Lemma D_7a724 : decode_any W_7a724 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a728 : bv 32 := 0x00355513.
Lemma F_7a728 : fetch_word AsanUbsan.M.loaded_segments (0x7a778 : word) = Some W_7a728.
Proof. vm_refl. Qed.
Lemma D_7a728 : decode_any W_7a728 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a72c : bv 32 := 0x00a58533.
Lemma F_7a72c : fetch_word AsanUbsan.M.loaded_segments (0x7a77c : word) = Some W_7a72c.
Proof. vm_refl. Qed.
Lemma D_7a72c : decode_any W_7a72c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a730 : bv 32 := 0x00008067.
Lemma F_7a730 : fetch_word AsanUbsan.M.loaded_segments (0x7a780 : word) = Some W_7a730.
Proof. vm_refl. Qed.
Lemma D_7a730 : decode_any W_7a730 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
