(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_147144 : bv 32 := 0x0056b597.
Lemma F_147144 : fetch_word AsanUbsan.M.loaded_segments (0x147180 : word) = Some W_147144.
Proof. vm_refl. Qed.
Lemma D_147144 : decode_any W_147144 = Some (Auipc 11 1387, 4%Z).
Proof. vm_refl. Qed.

Definition W_147148 : bv 32 := 0xea358683.
Lemma F_147148 : fetch_word AsanUbsan.M.loaded_segments (0x147184 : word) = Some W_147148.
Proof. vm_refl. Qed.
Lemma D_147148 : decode_any W_147148 = Some (Load SZ1 true 13 11 3747, 4%Z).
Proof. vm_refl. Qed.

Definition W_14714c : bv 32 := 0x1e068863.
Lemma F_14714c : fetch_word AsanUbsan.M.loaded_segments (0x147188 : word) = Some W_14714c.
Proof. vm_refl. Qed.
Lemma D_14714c : decode_any W_14714c = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_14733c : bv 32 := 0x00008067.
Lemma F_14733c : fetch_word AsanUbsan.M.loaded_segments (0x147378 : word) = Some W_14733c.
Proof. vm_refl. Qed.
Lemma D_14733c : decode_any W_14733c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1473cc : bv 32 := 0x00052583.
Lemma F_1473cc : fetch_word AsanUbsan.M.loaded_segments (0x147408 : word) = Some W_1473cc.
Proof. vm_refl. Qed.
Lemma D_1473cc : decode_any W_1473cc = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1473d0 : bv 32 := 0x0005c463.
Lemma F_1473d0 : fetch_word AsanUbsan.M.loaded_segments (0x14740c : word) = Some W_1473d0.
Proof. vm_refl. Qed.
Lemma D_1473d0 : decode_any W_1473d0 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1473d4 : bv 32 := 0x00008067.
Lemma F_1473d4 : fetch_word AsanUbsan.M.loaded_segments (0x147410 : word) = Some W_1473d4.
Proof. vm_refl. Qed.
Lemma D_1473d4 : decode_any W_1473d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_147440 : bv 32 := 0x00050893.
Lemma F_147440 : fetch_word AsanUbsan.M.loaded_segments (0x14747c : word) = Some W_147440.
Proof. vm_refl. Qed.
Lemma D_147440 : decode_any W_147440 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_147444 : bv 32 := 0x00058513.
Lemma F_147444 : fetch_word AsanUbsan.M.loaded_segments (0x147480 : word) = Some W_147444.
Proof. vm_refl. Qed.
Lemma D_147444 : decode_any W_147444 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_147448 : bv 32 := 0x00060593.
Lemma F_147448 : fetch_word AsanUbsan.M.loaded_segments (0x147484 : word) = Some W_147448.
Proof. vm_refl. Qed.
Lemma D_147448 : decode_any W_147448 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14744c : bv 32 := 0x00068613.
Lemma F_14744c : fetch_word AsanUbsan.M.loaded_segments (0x147488 : word) = Some W_14744c.
Proof. vm_refl. Qed.
Lemma D_14744c : decode_any W_14744c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_147450 : bv 32 := 0x00070693.
Lemma F_147450 : fetch_word AsanUbsan.M.loaded_segments (0x14748c : word) = Some W_147450.
Proof. vm_refl. Qed.
Lemma D_147450 : decode_any W_147450 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_147454 : bv 32 := 0x00078713.
Lemma F_147454 : fetch_word AsanUbsan.M.loaded_segments (0x147490 : word) = Some W_147454.
Proof. vm_refl. Qed.
Lemma D_147454 : decode_any W_147454 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_147458 : bv 32 := 0x00080793.
Lemma F_147458 : fetch_word AsanUbsan.M.loaded_segments (0x147494 : word) = Some W_147458.
Proof. vm_refl. Qed.
Lemma D_147458 : decode_any W_147458 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_147460 : bv 32 := 0x00008067.
Lemma F_147460 : fetch_word AsanUbsan.M.loaded_segments (0x14749c : word) = Some W_147460.
Proof. vm_refl. Qed.
Lemma D_147460 : decode_any W_147460 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_147464 : bv 32 := 0xfddff06f.
Lemma F_147464 : fetch_word AsanUbsan.M.loaded_segments (0x1474a0 : word) = Some W_147464.
Proof. vm_refl. Qed.
Lemma D_147464 : decode_any W_147464 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition W_147468 : bv 32 := 0x00020593.
Lemma F_147468 : fetch_word AsanUbsan.M.loaded_segments (0x1474a4 : word) = Some W_147468.
Proof. vm_refl. Qed.
Lemma D_147468 : decode_any W_147468 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14746c : bv 32 := 0x00053603.
Lemma F_14746c : fetch_word AsanUbsan.M.loaded_segments (0x1474a8 : word) = Some W_14746c.
Proof. vm_refl. Qed.
Lemma D_14746c : decode_any W_14746c = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_147470 : bv 32 := 0xff85b583.
Lemma F_147470 : fetch_word AsanUbsan.M.loaded_segments (0x1474ac : word) = Some W_147470.
Proof. vm_refl. Qed.
Lemma D_147470 : decode_any W_147470 = Some (Load SZ8 true 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_147474 : bv 32 := 0x00853503.
Lemma F_147474 : fetch_word AsanUbsan.M.loaded_segments (0x1474b0 : word) = Some W_147474.
Proof. vm_refl. Qed.
Lemma D_147474 : decode_any W_147474 = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_147478 : bv 32 := 0x00361613.
Lemma F_147478 : fetch_word AsanUbsan.M.loaded_segments (0x1474b4 : word) = Some W_147478.
Proof. vm_refl. Qed.
Lemma D_147478 : decode_any W_147478 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_14747c : bv 32 := 0x00c585b3.
Lemma F_14747c : fetch_word AsanUbsan.M.loaded_segments (0x1474b8 : word) = Some W_14747c.
Proof. vm_refl. Qed.
Lemma D_14747c : decode_any W_14747c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_147480 : bv 32 := 0x0005b583.
Lemma F_147480 : fetch_word AsanUbsan.M.loaded_segments (0x1474bc : word) = Some W_147480.
Proof. vm_refl. Qed.
Lemma D_147480 : decode_any W_147480 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_147484 : bv 32 := 0x00b50533.
Lemma F_147484 : fetch_word AsanUbsan.M.loaded_segments (0x1474c0 : word) = Some W_147484.
Proof. vm_refl. Qed.
Lemma D_147484 : decode_any W_147484 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_147488 : bv 32 := 0x00008067.
Lemma F_147488 : fetch_word AsanUbsan.M.loaded_segments (0x1474c4 : word) = Some W_147488.
Proof. vm_refl. Qed.
Lemma D_147488 : decode_any W_147488 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

