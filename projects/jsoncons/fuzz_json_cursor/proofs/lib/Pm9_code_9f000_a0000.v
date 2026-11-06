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

Definition W_9f000 : bv 32 := 0x03013403.
Lemma F_9f000 : fetch_word AsanUbsan.M.loaded_segments (0x9f048 : word) = Some W_9f000.
Proof. vm_refl. Qed.
Lemma D_9f000 : decode_any W_9f000 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f004 : bv 32 := 0x02813483.
Lemma F_9f004 : fetch_word AsanUbsan.M.loaded_segments (0x9f04c : word) = Some W_9f004.
Proof. vm_refl. Qed.
Lemma D_9f004 : decode_any W_9f004 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f008 : bv 32 := 0x02013903.
Lemma F_9f008 : fetch_word AsanUbsan.M.loaded_segments (0x9f050 : word) = Some W_9f008.
Proof. vm_refl. Qed.
Lemma D_9f008 : decode_any W_9f008 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f00c : bv 32 := 0x01813983.
Lemma F_9f00c : fetch_word AsanUbsan.M.loaded_segments (0x9f054 : word) = Some W_9f00c.
Proof. vm_refl. Qed.
Lemma D_9f00c : decode_any W_9f00c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f010 : bv 32 := 0x01013a03.
Lemma F_9f010 : fetch_word AsanUbsan.M.loaded_segments (0x9f058 : word) = Some W_9f010.
Proof. vm_refl. Qed.
Lemma D_9f010 : decode_any W_9f010 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f014 : bv 32 := 0x00813a83.
Lemma F_9f014 : fetch_word AsanUbsan.M.loaded_segments (0x9f05c : word) = Some W_9f014.
Proof. vm_refl. Qed.
Lemma D_9f014 : decode_any W_9f014 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f018 : bv 32 := 0x04010113.
Lemma F_9f018 : fetch_word AsanUbsan.M.loaded_segments (0x9f060 : word) = Some W_9f018.
Proof. vm_refl. Qed.
Lemma D_9f018 : decode_any W_9f018 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f01c : bv 32 := 0x00008067.
Lemma F_9f01c : fetch_word AsanUbsan.M.loaded_segments (0x9f064 : word) = Some W_9f01c.
Proof. vm_refl. Qed.
Lemma D_9f01c : decode_any W_9f01c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f044 : bv 32 := 0xff010113.
Lemma F_9f044 : fetch_word AsanUbsan.M.loaded_segments (0x9f08c : word) = Some W_9f044.
Proof. vm_refl. Qed.
Lemma D_9f044 : decode_any W_9f044 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f048 : bv 32 := 0x00113423.
Lemma F_9f048 : fetch_word AsanUbsan.M.loaded_segments (0x9f090 : word) = Some W_9f048.
Proof. vm_refl. Qed.
Lemma D_9f048 : decode_any W_9f048 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f04c : bv 32 := 0x00813023.
Lemma F_9f04c : fetch_word AsanUbsan.M.loaded_segments (0x9f094 : word) = Some W_9f04c.
Proof. vm_refl. Qed.
Lemma D_9f04c : decode_any W_9f04c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f050 : bv 32 := 0x00058793.
Lemma F_9f050 : fetch_word AsanUbsan.M.loaded_segments (0x9f098 : word) = Some W_9f050.
Proof. vm_refl. Qed.
Lemma D_9f050 : decode_any W_9f050 = Some (OpImm ALU_ADD 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f054 : bv 32 := 0x00050593.
Lemma F_9f054 : fetch_word AsanUbsan.M.loaded_segments (0x9f09c : word) = Some W_9f054.
Proof. vm_refl. Qed.
Lemma D_9f054 : decode_any W_9f054 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f058 : bv 32 := 0x00f5342f.
Lemma F_9f058 : fetch_word AsanUbsan.M.loaded_segments (0x9f0a0 : word) = Some W_9f058.
Proof. vm_refl. Qed.
Lemma D_9f058 : decode_any W_9f058 = Some (Amo AMO_ADD AD false false 8 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f05c : bv 32 := 0xfff78513.
Lemma F_9f05c : fetch_word AsanUbsan.M.loaded_segments (0x9f0a4 : word) = Some W_9f05c.
Proof. vm_refl. Qed.
Lemma D_9f05c : decode_any W_9f05c = Some (OpImm ALU_ADD 10 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f060 : bv 32 := 0x01445293.
Lemma F_9f060 : fetch_word AsanUbsan.M.loaded_segments (0x9f0a8 : word) = Some W_9f060.
Proof. vm_refl. Qed.
Lemma D_9f060 : decode_any W_9f060 = Some (ShiftImm ALU_SRL 5 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f064 : bv 32 := 0x00850733.
Lemma F_9f064 : fetch_word AsanUbsan.M.loaded_segments (0x9f0ac : word) = Some W_9f064.
Proof. vm_refl. Qed.
Lemma D_9f064 : decode_any W_9f064 = Some (Op ALU_ADD 14 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f068 : bv 32 := 0x01475313.
Lemma F_9f068 : fetch_word AsanUbsan.M.loaded_segments (0x9f0b0 : word) = Some W_9f068.
Proof. vm_refl. Qed.
Lemma D_9f068 : decode_any W_9f068 = Some (ShiftImm ALU_SRL 6 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f06c : bv 32 := 0x04629863.
Lemma F_9f06c : fetch_word AsanUbsan.M.loaded_segments (0x9f0b4 : word) = Some W_9f06c.
Proof. vm_refl. Qed.
Lemma D_9f06c : decode_any W_9f06c = Some (Branch BC_NE 5 6 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f070 : bv 32 := 0x02045513.
Lemma F_9f070 : fetch_word AsanUbsan.M.loaded_segments (0x9f0b8 : word) = Some W_9f070.
Proof. vm_refl. Qed.
Lemma D_9f070 : decode_any W_9f070 = Some (ShiftImm ALU_SRL 10 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f074 : bv 32 := 0x00050c63.
Lemma F_9f074 : fetch_word AsanUbsan.M.loaded_segments (0x9f0bc : word) = Some W_9f074.
Proof. vm_refl. Qed.
Lemma D_9f074 : decode_any W_9f074 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f08c : bv 32 := 0x00863023.
Lemma F_9f08c : fetch_word AsanUbsan.M.loaded_segments (0x9f0d4 : word) = Some W_9f08c.
Proof. vm_refl. Qed.
Lemma D_9f08c : decode_any W_9f08c = Some (Store SZ8 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f090 : bv 32 := 0x00429613.
Lemma F_9f090 : fetch_word AsanUbsan.M.loaded_segments (0x9f0d8 : word) = Some W_9f090.
Proof. vm_refl. Qed.
Lemma D_9f090 : decode_any W_9f090 = Some (ShiftImm ALU_SLL 12 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f094 : bv 32 := 0x00c58633.
Lemma F_9f094 : fetch_word AsanUbsan.M.loaded_segments (0x9f0dc : word) = Some W_9f094.
Proof. vm_refl. Qed.
Lemma D_9f094 : decode_any W_9f094 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f098 : bv 32 := 0x01063503.
Lemma F_9f098 : fetch_word AsanUbsan.M.loaded_segments (0x9f0e0 : word) = Some W_9f098.
Proof. vm_refl. Qed.
Lemma D_9f098 : decode_any W_9f098 = Some (Load SZ8 true 10 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f09c : bv 32 := 0x0a050a63.
Lemma F_9f09c : fetch_word AsanUbsan.M.loaded_segments (0x9f0e4 : word) = Some W_9f09c.
Proof. vm_refl. Qed.
Lemma D_9f09c : decode_any W_9f09c = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f0a0 : bv 32 := 0x02c41413.
Lemma F_9f0a0 : fetch_word AsanUbsan.M.loaded_segments (0x9f0e8 : word) = Some W_9f0a0.
Proof. vm_refl. Qed.
Lemma D_9f0a0 : decode_any W_9f0a0 = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f0a4 : bv 32 := 0x02945413.
Lemma F_9f0a4 : fetch_word AsanUbsan.M.loaded_segments (0x9f0ec : word) = Some W_9f0a4.
Proof. vm_refl. Qed.
Lemma D_9f0a4 : decode_any W_9f0a4 = Some (ShiftImm ALU_SRL 8 8 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f0a8 : bv 32 := 0x00850533.
Lemma F_9f0a8 : fetch_word AsanUbsan.M.loaded_segments (0x9f0f0 : word) = Some W_9f0a8.
Proof. vm_refl. Qed.
Lemma D_9f0a8 : decode_any W_9f0a8 = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f0ac : bv 32 := 0x00813083.
Lemma F_9f0ac : fetch_word AsanUbsan.M.loaded_segments (0x9f0f4 : word) = Some W_9f0ac.
Proof. vm_refl. Qed.
Lemma D_9f0ac : decode_any W_9f0ac = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f0b0 : bv 32 := 0x00013403.
Lemma F_9f0b0 : fetch_word AsanUbsan.M.loaded_segments (0x9f0f8 : word) = Some W_9f0b0.
Proof. vm_refl. Qed.
Lemma D_9f0b0 : decode_any W_9f0b0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f0b4 : bv 32 := 0x01010113.
Lemma F_9f0b4 : fetch_word AsanUbsan.M.loaded_segments (0x9f0fc : word) = Some W_9f0b4.
Proof. vm_refl. Qed.
Lemma D_9f0b4 : decode_any W_9f0b4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9f0b8 : bv 32 := 0x00008067.
Lemma F_9f0b8 : fetch_word AsanUbsan.M.loaded_segments (0x9f100 : word) = Some W_9f0b8.
Proof. vm_refl. Qed.
Lemma D_9f0b8 : decode_any W_9f0b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

