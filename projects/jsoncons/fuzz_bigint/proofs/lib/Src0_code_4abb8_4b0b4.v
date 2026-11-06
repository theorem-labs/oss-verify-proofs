(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_4abb8 : bv 32 := 0x00008067.
Lemma F_4abb8 : fetch_word Plain.M.loaded_segments (0x4abb8 : word) = Some W_4abb8.
Proof. vm_refl. Qed.
Lemma D_4abb8 : decode_any W_4abb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abbc : bv 32 := 0xe8010113.
Lemma F_4abbc : fetch_word Plain.M.loaded_segments (0x4abbc : word) = Some W_4abbc.
Proof. vm_refl. Qed.
Lemma D_4abbc : decode_any W_4abbc = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abc0 : bv 32 := 0x16113c23.
Lemma F_4abc0 : fetch_word Plain.M.loaded_segments (0x4abc0 : word) = Some W_4abc0.
Proof. vm_refl. Qed.
Lemma D_4abc0 : decode_any W_4abc0 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abc4 : bv 32 := 0x16813823.
Lemma F_4abc4 : fetch_word Plain.M.loaded_segments (0x4abc4 : word) = Some W_4abc4.
Proof. vm_refl. Qed.
Lemma D_4abc4 : decode_any W_4abc4 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abc8 : bv 32 := 0x16913423.
Lemma F_4abc8 : fetch_word Plain.M.loaded_segments (0x4abc8 : word) = Some W_4abc8.
Proof. vm_refl. Qed.
Lemma D_4abc8 : decode_any W_4abc8 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abcc : bv 32 := 0x17213023.
Lemma F_4abcc : fetch_word Plain.M.loaded_segments (0x4abcc : word) = Some W_4abcc.
Proof. vm_refl. Qed.
Lemma D_4abcc : decode_any W_4abcc = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abd0 : bv 32 := 0x00058413.
Lemma F_4abd0 : fetch_word Plain.M.loaded_segments (0x4abd0 : word) = Some W_4abd0.
Proof. vm_refl. Qed.
Lemma D_4abd0 : decode_any W_4abd0 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abd4 : bv 32 := 0x00050493.
Lemma F_4abd4 : fetch_word Plain.M.loaded_segments (0x4abd4 : word) = Some W_4abd4.
Proof. vm_refl. Qed.
Lemma D_4abd4 : decode_any W_4abd4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abd8 : bv 32 := 0x03010513.
Lemma F_4abd8 : fetch_word Plain.M.loaded_segments (0x4abd8 : word) = Some W_4abd8.
Proof. vm_refl. Qed.
Lemma D_4abd8 : decode_any W_4abd8 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abdc : bv 32 := 0x13000613.
Lemma F_4abdc : fetch_word Plain.M.loaded_segments (0x4abdc : word) = Some W_4abdc.
Proof. vm_refl. Qed.
Lemma D_4abdc : decode_any W_4abdc = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abe0 : bv 32 := 0x00000593.
Lemma F_4abe0 : fetch_word Plain.M.loaded_segments (0x4abe0 : word) = Some W_4abe0.
Proof. vm_refl. Qed.
Lemma D_4abe0 : decode_any W_4abe0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abe4 : bv 32 := 0x2c00e0ef.
Lemma F_4abe4 : fetch_word Plain.M.loaded_segments (0x4abe4 : word) = Some W_4abe4.
Proof. vm_refl. Qed.
Lemma D_4abe4 : decode_any W_4abe4 = Some (Jal 1 58048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abe8 : bv 32 := 0x00014517.
Lemma F_4abe8 : fetch_word Plain.M.loaded_segments (0x4abe8 : word) = Some W_4abe8.
Proof. vm_refl. Qed.
Lemma D_4abe8 : decode_any W_4abe8 = Some (Auipc 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abec : bv 32 := 0x9e053503.
Lemma F_4abec : fetch_word Plain.M.loaded_segments (0x4abec : word) = Some W_4abec.
Proof. vm_refl. Qed.
Lemma D_4abec : decode_any W_4abec = Some (Load SZ8 true 10 10 2528, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abf0 : bv 32 := 0x00953023.
Lemma F_4abf0 : fetch_word Plain.M.loaded_segments (0x4abf0 : word) = Some W_4abf0.
Proof. vm_refl. Qed.
Lemma D_4abf0 : decode_any W_4abf0 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abf4 : bv 32 := 0x0004b503.
Lemma F_4abf4 : fetch_word Plain.M.loaded_segments (0x4abf4 : word) = Some W_4abf4.
Proof. vm_refl. Qed.
Lemma D_4abf4 : decode_any W_4abf4 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abf8 : bv 32 := 0x00848493.
Lemma F_4abf8 : fetch_word Plain.M.loaded_segments (0x4abf8 : word) = Some W_4abf8.
Proof. vm_refl. Qed.
Lemma D_4abf8 : decode_any W_4abf8 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4abfc : bv 32 := 0xfe051ce3.
Lemma F_4abfc : fetch_word Plain.M.loaded_segments (0x4abfc : word) = Some W_4abfc.
Proof. vm_refl. Qed.
Lemma D_4abfc : decode_any W_4abfc = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac00 : bv 32 := 0x00046517.
Lemma F_4ac00 : fetch_word Plain.M.loaded_segments (0x4ac00 : word) = Some W_4ac00.
Proof. vm_refl. Qed.
Lemma D_4ac00 : decode_any W_4ac00 = Some (Auipc 10 70, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac04 : bv 32 := 0xac850913.
Lemma F_4ac04 : fetch_word Plain.M.loaded_segments (0x4ac04 : word) = Some W_4ac04.
Proof. vm_refl. Qed.
Lemma D_4ac04 : decode_any W_4ac04 = Some (OpImm ALU_ADD 18 10 2760, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac08 : bv 32 := 0x00993423.
Lemma F_4ac08 : fetch_word Plain.M.loaded_segments (0x4ac08 : word) = Some W_4ac08.
Proof. vm_refl. Qed.
Lemma D_4ac08 : decode_any W_4ac08 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac0c : bv 32 := 0x0004b583.
Lemma F_4ac0c : fetch_word Plain.M.loaded_segments (0x4ac0c : word) = Some W_4ac0c.
Proof. vm_refl. Qed.
Lemma D_4ac0c : decode_any W_4ac0c = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac10 : bv 32 := 0x04058c63.
Lemma F_4ac10 : fetch_word Plain.M.loaded_segments (0x4ac10 : word) = Some W_4ac10.
Proof. vm_refl. Qed.
Lemma D_4ac10 : decode_any W_4ac10 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac14 : bv 32 := 0x01048493.
Lemma F_4ac14 : fetch_word Plain.M.loaded_segments (0x4ac14 : word) = Some W_4ac14.
Proof. vm_refl. Qed.
Lemma D_4ac14 : decode_any W_4ac14 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac18 : bv 32 := 0x02500513.
Lemma F_4ac18 : fetch_word Plain.M.loaded_segments (0x4ac18 : word) = Some W_4ac18.
Proof. vm_refl. Qed.
Lemma D_4ac18 : decode_any W_4ac18 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac1c : bv 32 := 0x03010613.
Lemma F_4ac1c : fetch_word Plain.M.loaded_segments (0x4ac1c : word) = Some W_4ac1c.
Proof. vm_refl. Qed.
Lemma D_4ac1c : decode_any W_4ac1c = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac20 : bv 32 := 0x0100006f.
Lemma F_4ac20 : fetch_word Plain.M.loaded_segments (0x4ac20 : word) = Some W_4ac20.
Proof. vm_refl. Qed.
Lemma D_4ac20 : decode_any W_4ac20 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac24 : bv 32 := 0x0004b583.
Lemma F_4ac24 : fetch_word Plain.M.loaded_segments (0x4ac24 : word) = Some W_4ac24.
Proof. vm_refl. Qed.
Lemma D_4ac24 : decode_any W_4ac24 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac28 : bv 32 := 0x01048493.
Lemma F_4ac28 : fetch_word Plain.M.loaded_segments (0x4ac28 : word) = Some W_4ac28.
Proof. vm_refl. Qed.
Lemma D_4ac28 : decode_any W_4ac28 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac2c : bv 32 := 0x00058e63.
Lemma F_4ac2c : fetch_word Plain.M.loaded_segments (0x4ac2c : word) = Some W_4ac2c.
Proof. vm_refl. Qed.
Lemma D_4ac2c : decode_any W_4ac2c = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac30 : bv 32 := 0xfeb56ae3.
Lemma F_4ac30 : fetch_word Plain.M.loaded_segments (0x4ac30 : word) = Some W_4ac30.
Proof. vm_refl. Qed.
Lemma D_4ac30 : decode_any W_4ac30 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac34 : bv 32 := 0xff84b683.
Lemma F_4ac34 : fetch_word Plain.M.loaded_segments (0x4ac34 : word) = Some W_4ac34.
Proof. vm_refl. Qed.
Lemma D_4ac34 : decode_any W_4ac34 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac38 : bv 32 := 0x00359593.
Lemma F_4ac38 : fetch_word Plain.M.loaded_segments (0x4ac38 : word) = Some W_4ac38.
Proof. vm_refl. Qed.
Lemma D_4ac38 : decode_any W_4ac38 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac3c : bv 32 := 0x00b605b3.
Lemma F_4ac3c : fetch_word Plain.M.loaded_segments (0x4ac3c : word) = Some W_4ac3c.
Proof. vm_refl. Qed.
Lemma D_4ac3c : decode_any W_4ac3c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac40 : bv 32 := 0x00d5b023.
Lemma F_4ac40 : fetch_word Plain.M.loaded_segments (0x4ac40 : word) = Some W_4ac40.
Proof. vm_refl. Qed.
Lemma D_4ac40 : decode_any W_4ac40 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac44 : bv 32 := 0xfe1ff06f.
Lemma F_4ac44 : fetch_word Plain.M.loaded_segments (0x4ac44 : word) = Some W_4ac44.
Proof. vm_refl. Qed.
Lemma D_4ac44 : decode_any W_4ac44 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac48 : bv 32 := 0x0b013583.
Lemma F_4ac48 : fetch_word Plain.M.loaded_segments (0x4ac48 : word) = Some W_4ac48.
Proof. vm_refl. Qed.
Lemma D_4ac48 : decode_any W_4ac48 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac4c : bv 32 := 0x13013503.
Lemma F_4ac4c : fetch_word Plain.M.loaded_segments (0x4ac4c : word) = Some W_4ac4c.
Proof. vm_refl. Qed.
Lemma D_4ac4c : decode_any W_4ac4c = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac50 : bv 32 := 0x00046617.
Lemma F_4ac50 : fetch_word Plain.M.loaded_segments (0x4ac50 : word) = Some W_4ac50.
Proof. vm_refl. Qed.
Lemma D_4ac50 : decode_any W_4ac50 = Some (Auipc 12 70, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac54 : bv 32 := 0xaeb63023.
Lemma F_4ac54 : fetch_word Plain.M.loaded_segments (0x4ac54 : word) = Some W_4ac54.
Proof. vm_refl. Qed.
Lemma D_4ac54 : decode_any W_4ac54 = Some (Store SZ8 12 11 2784, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac58 : bv 32 := 0x00050c63.
Lemma F_4ac58 : fetch_word Plain.M.loaded_segments (0x4ac58 : word) = Some W_4ac58.
Proof. vm_refl. Qed.
Lemma D_4ac58 : decode_any W_4ac58 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac70 : bv 32 := 0x06013503.
Lemma F_4ac70 : fetch_word Plain.M.loaded_segments (0x4ac70 : word) = Some W_4ac70.
Proof. vm_refl. Qed.
Lemma D_4ac70 : decode_any W_4ac70 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac74 : bv 32 := 0x02a93823.
Lemma F_4ac74 : fetch_word Plain.M.loaded_segments (0x4ac74 : word) = Some W_4ac74.
Proof. vm_refl. Qed.
Lemma D_4ac74 : decode_any W_4ac74 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac78 : bv 32 := 0x00041463.
Lemma F_4ac78 : fetch_word Plain.M.loaded_segments (0x4ac78 : word) = Some W_4ac78.
Proof. vm_refl. Qed.
Lemma D_4ac78 : decode_any W_4ac78 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac80 : bv 32 := 0x00041663.
Lemma F_4ac80 : fetch_word Plain.M.loaded_segments (0x4ac80 : word) = Some W_4ac80.
Proof. vm_refl. Qed.
Lemma D_4ac80 : decode_any W_4ac80 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac8c : bv 32 := 0x00014517.
Lemma F_4ac8c : fetch_word Plain.M.loaded_segments (0x4ac8c : word) = Some W_4ac8c.
Proof. vm_refl. Qed.
Lemma D_4ac8c : decode_any W_4ac8c = Some (Auipc 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac90 : bv 32 := 0x94453583.
Lemma F_4ac90 : fetch_word Plain.M.loaded_segments (0x4ac90 : word) = Some W_4ac90.
Proof. vm_refl. Qed.
Lemma D_4ac90 : decode_any W_4ac90 = Some (Load SZ8 true 11 10 2372, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac94 : bv 32 := 0x00014517.
Lemma F_4ac94 : fetch_word Plain.M.loaded_segments (0x4ac94 : word) = Some W_4ac94.
Proof. vm_refl. Qed.
Lemma D_4ac94 : decode_any W_4ac94 = Some (Auipc 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac98 : bv 32 := 0x94453503.
Lemma F_4ac98 : fetch_word Plain.M.loaded_segments (0x4ac98 : word) = Some W_4ac98.
Proof. vm_refl. Qed.
Lemma D_4ac98 : decode_any W_4ac98 = Some (Load SZ8 true 10 10 2372, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ac9c : bv 32 := 0x0085b023.
Lemma F_4ac9c : fetch_word Plain.M.loaded_segments (0x4ac9c : word) = Some W_4ac9c.
Proof. vm_refl. Qed.
Lemma D_4ac9c : decode_any W_4ac9c = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aca0 : bv 32 := 0x00140593.
Lemma F_4aca0 : fetch_word Plain.M.loaded_segments (0x4aca0 : word) = Some W_4aca0.
Proof. vm_refl. Qed.
Lemma D_4aca0 : decode_any W_4aca0 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aca4 : bv 32 := 0x00853023.
Lemma F_4aca4 : fetch_word Plain.M.loaded_segments (0x4aca4 : word) = Some W_4aca4.
Proof. vm_refl. Qed.
Lemma D_4aca4 : decode_any W_4aca4 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aca8 : bv 32 := 0x02f00613.
Lemma F_4aca8 : fetch_word Plain.M.loaded_segments (0x4aca8 : word) = Some W_4aca8.
Proof. vm_refl. Qed.
Lemma D_4aca8 : decode_any W_4aca8 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acac : bv 32 := 0x00c0006f.
Lemma F_4acac : fetch_word Plain.M.loaded_segments (0x4acac : word) = Some W_4acac.
Proof. vm_refl. Qed.
Lemma D_4acac : decode_any W_4acac = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acb0 : bv 32 := 0x00b53023.
Lemma F_4acb0 : fetch_word Plain.M.loaded_segments (0x4acb0 : word) = Some W_4acb0.
Proof. vm_refl. Qed.
Lemma D_4acb0 : decode_any W_4acb0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acb4 : bv 32 := 0x00158593.
Lemma F_4acb4 : fetch_word Plain.M.loaded_segments (0x4acb4 : word) = Some W_4acb4.
Proof. vm_refl. Qed.
Lemma D_4acb4 : decode_any W_4acb4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acb8 : bv 32 := 0xfff5c683.
Lemma F_4acb8 : fetch_word Plain.M.loaded_segments (0x4acb8 : word) = Some W_4acb8.
Proof. vm_refl. Qed.
Lemma D_4acb8 : decode_any W_4acb8 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acbc : bv 32 := 0xfec68ae3.
Lemma F_4acbc : fetch_word Plain.M.loaded_segments (0x4acbc : word) = Some W_4acbc.
Proof. vm_refl. Qed.
Lemma D_4acbc : decode_any W_4acbc = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acc0 : bv 32 := 0xfe069ae3.
Lemma F_4acc0 : fetch_word Plain.M.loaded_segments (0x4acc0 : word) = Some W_4acc0.
Proof. vm_refl. Qed.
Lemma D_4acc0 : decode_any W_4acc0 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acc4 : bv 32 := 0x03010513.
Lemma F_4acc4 : fetch_word Plain.M.loaded_segments (0x4acc4 : word) = Some W_4acc4.
Proof. vm_refl. Qed.
Lemma D_4acc4 : decode_any W_4acc4 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acc8 : bv 32 := 0x214000ef.
Lemma F_4acc8 : fetch_word Plain.M.loaded_segments (0x4acc8 : word) = Some W_4acc8.
Proof. vm_refl. Qed.
Lemma D_4acc8 : decode_any W_4acc8 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_4accc : bv 32 := 0x0f813503.
Lemma F_4accc : fetch_word Plain.M.loaded_segments (0x4accc : word) = Some W_4accc.
Proof. vm_refl. Qed.
Lemma D_4accc : decode_any W_4accc = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acd0 : bv 32 := 0x0e5000ef.
Lemma F_4acd0 : fetch_word Plain.M.loaded_segments (0x4acd0 : word) = Some W_4acd0.
Proof. vm_refl. Qed.
Lemma D_4acd0 : decode_any W_4acd0 = Some (Jal 1 2276, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acd4 : bv 32 := 0x08813503.
Lemma F_4acd4 : fetch_word Plain.M.loaded_segments (0x4acd4 : word) = Some W_4acd4.
Proof. vm_refl. Qed.
Lemma D_4acd4 : decode_any W_4acd4 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acd8 : bv 32 := 0x09013583.
Lemma F_4acd8 : fetch_word Plain.M.loaded_segments (0x4acd8 : word) = Some W_4acd8.
Proof. vm_refl. Qed.
Lemma D_4acd8 : decode_any W_4acd8 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acdc : bv 32 := 0x00b51c63.
Lemma F_4acdc : fetch_word Plain.M.loaded_segments (0x4acdc : word) = Some W_4acdc.
Proof. vm_refl. Qed.
Lemma D_4acdc : decode_any W_4acdc = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ace0 : bv 32 := 0x09813503.
Lemma F_4ace0 : fetch_word Plain.M.loaded_segments (0x4ace0 : word) = Some W_4ace0.
Proof. vm_refl. Qed.
Lemma D_4ace0 : decode_any W_4ace0 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ace4 : bv 32 := 0x0a013583.
Lemma F_4ace4 : fetch_word Plain.M.loaded_segments (0x4ace4 : word) = Some W_4ace4.
Proof. vm_refl. Qed.
Lemma D_4ace4 : decode_any W_4ace4 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ace8 : bv 32 := 0x00b51663.
Lemma F_4ace8 : fetch_word Plain.M.loaded_segments (0x4ace8 : word) = Some W_4ace8.
Proof. vm_refl. Qed.
Lemma D_4ace8 : decode_any W_4ace8 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acec : bv 32 := 0x0e813503.
Lemma F_4acec : fetch_word Plain.M.loaded_segments (0x4acec : word) = Some W_4acec.
Proof. vm_refl. Qed.
Lemma D_4acec : decode_any W_4acec = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_4acf0 : bv 32 := 0x0e050063.
Lemma F_4acf0 : fetch_word Plain.M.loaded_segments (0x4acf0 : word) = Some W_4acf0.
Proof. vm_refl. Qed.
Lemma D_4acf0 : decode_any W_4acf0 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_4add0 : bv 32 := 0x17813083.
Lemma F_4add0 : fetch_word Plain.M.loaded_segments (0x4add0 : word) = Some W_4add0.
Proof. vm_refl. Qed.
Lemma D_4add0 : decode_any W_4add0 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_4add4 : bv 32 := 0x17013403.
Lemma F_4add4 : fetch_word Plain.M.loaded_segments (0x4add4 : word) = Some W_4add4.
Proof. vm_refl. Qed.
Lemma D_4add4 : decode_any W_4add4 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_4add8 : bv 32 := 0x16813483.
Lemma F_4add8 : fetch_word Plain.M.loaded_segments (0x4add8 : word) = Some W_4add8.
Proof. vm_refl. Qed.
Lemma D_4add8 : decode_any W_4add8 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_4addc : bv 32 := 0x16013903.
Lemma F_4addc : fetch_word Plain.M.loaded_segments (0x4addc : word) = Some W_4addc.
Proof. vm_refl. Qed.
Lemma D_4addc : decode_any W_4addc = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ade0 : bv 32 := 0x18010113.
Lemma F_4ade0 : fetch_word Plain.M.loaded_segments (0x4ade0 : word) = Some W_4ade0.
Proof. vm_refl. Qed.
Lemma D_4ade0 : decode_any W_4ade0 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ade4 : bv 32 := 0x00008067.
Lemma F_4ade4 : fetch_word Plain.M.loaded_segments (0x4ade4 : word) = Some W_4ade4.
Proof. vm_refl. Qed.
Lemma D_4ade4 : decode_any W_4ade4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ade8 : bv 32 := 0xfe010113.
Lemma F_4ade8 : fetch_word Plain.M.loaded_segments (0x4ade8 : word) = Some W_4ade8.
Proof. vm_refl. Qed.
Lemma D_4ade8 : decode_any W_4ade8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4adec : bv 32 := 0x00113c23.
Lemma F_4adec : fetch_word Plain.M.loaded_segments (0x4adec : word) = Some W_4adec.
Proof. vm_refl. Qed.
Lemma D_4adec : decode_any W_4adec = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4adf0 : bv 32 := 0x00813823.
Lemma F_4adf0 : fetch_word Plain.M.loaded_segments (0x4adf0 : word) = Some W_4adf0.
Proof. vm_refl. Qed.
Lemma D_4adf0 : decode_any W_4adf0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4adf4 : bv 32 := 0x00913423.
Lemma F_4adf4 : fetch_word Plain.M.loaded_segments (0x4adf4 : word) = Some W_4adf4.
Proof. vm_refl. Qed.
Lemma D_4adf4 : decode_any W_4adf4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4adf8 : bv 32 := 0xdc1ff0ef.
Lemma F_4adf8 : fetch_word Plain.M.loaded_segments (0x4adf8 : word) = Some W_4adf8.
Proof. vm_refl. Qed.
Lemma D_4adf8 : decode_any W_4adf8 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_4adfc : bv 32 := 0x00013517.
Lemma F_4adfc : fetch_word Plain.M.loaded_segments (0x4adfc : word) = Some W_4adfc.
Proof. vm_refl. Qed.
Lemma D_4adfc : decode_any W_4adfc = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae00 : bv 32 := 0x00013597.
Lemma F_4ae00 : fetch_word Plain.M.loaded_segments (0x4ae00 : word) = Some W_4ae00.
Proof. vm_refl. Qed.
Lemma D_4ae00 : decode_any W_4ae00 = Some (Auipc 11 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae04 : bv 32 := 0x7e453403.
Lemma F_4ae04 : fetch_word Plain.M.loaded_segments (0x4ae04 : word) = Some W_4ae04.
Proof. vm_refl. Qed.
Lemma D_4ae04 : decode_any W_4ae04 = Some (Load SZ8 true 8 10 2020, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae08 : bv 32 := 0x7e85b483.
Lemma F_4ae08 : fetch_word Plain.M.loaded_segments (0x4ae08 : word) = Some W_4ae08.
Proof. vm_refl. Qed.
Lemma D_4ae08 : decode_any W_4ae08 = Some (Load SZ8 true 9 11 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae0c : bv 32 := 0x0084fa63.
Lemma F_4ae0c : fetch_word Plain.M.loaded_segments (0x4ae0c : word) = Some W_4ae0c.
Proof. vm_refl. Qed.
Lemma D_4ae0c : decode_any W_4ae0c = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae10 : bv 32 := 0x0004b503.
Lemma F_4ae10 : fetch_word Plain.M.loaded_segments (0x4ae10 : word) = Some W_4ae10.
Proof. vm_refl. Qed.
Lemma D_4ae10 : decode_any W_4ae10 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae14 : bv 32 := 0x000500e7.
Lemma F_4ae14 : fetch_word Plain.M.loaded_segments (0x4ae14 : word) = Some W_4ae14.
Proof. vm_refl. Qed.
Lemma D_4ae14 : decode_any W_4ae14 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae18 : bv 32 := 0x00848493.
Lemma F_4ae18 : fetch_word Plain.M.loaded_segments (0x4ae18 : word) = Some W_4ae18.
Proof. vm_refl. Qed.
Lemma D_4ae18 : decode_any W_4ae18 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae1c : bv 32 := 0xfe84eae3.
Lemma F_4ae1c : fetch_word Plain.M.loaded_segments (0x4ae1c : word) = Some W_4ae1c.
Proof. vm_refl. Qed.
Lemma D_4ae1c : decode_any W_4ae1c = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae20 : bv 32 := 0x01813083.
Lemma F_4ae20 : fetch_word Plain.M.loaded_segments (0x4ae20 : word) = Some W_4ae20.
Proof. vm_refl. Qed.
Lemma D_4ae20 : decode_any W_4ae20 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae24 : bv 32 := 0x01013403.
Lemma F_4ae24 : fetch_word Plain.M.loaded_segments (0x4ae24 : word) = Some W_4ae24.
Proof. vm_refl. Qed.
Lemma D_4ae24 : decode_any W_4ae24 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae28 : bv 32 := 0x00813483.
Lemma F_4ae28 : fetch_word Plain.M.loaded_segments (0x4ae28 : word) = Some W_4ae28.
Proof. vm_refl. Qed.
Lemma D_4ae28 : decode_any W_4ae28 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae2c : bv 32 := 0x02010113.
Lemma F_4ae2c : fetch_word Plain.M.loaded_segments (0x4ae2c : word) = Some W_4ae2c.
Proof. vm_refl. Qed.
Lemma D_4ae2c : decode_any W_4ae2c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae30 : bv 32 := 0x00008067.
Lemma F_4ae30 : fetch_word Plain.M.loaded_segments (0x4ae30 : word) = Some W_4ae30.
Proof. vm_refl. Qed.
Lemma D_4ae30 : decode_any W_4ae30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae34 : bv 32 := 0xfe010113.
Lemma F_4ae34 : fetch_word Plain.M.loaded_segments (0x4ae34 : word) = Some W_4ae34.
Proof. vm_refl. Qed.
Lemma D_4ae34 : decode_any W_4ae34 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae38 : bv 32 := 0x00113c23.
Lemma F_4ae38 : fetch_word Plain.M.loaded_segments (0x4ae38 : word) = Some W_4ae38.
Proof. vm_refl. Qed.
Lemma D_4ae38 : decode_any W_4ae38 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae3c : bv 32 := 0x00813823.
Lemma F_4ae3c : fetch_word Plain.M.loaded_segments (0x4ae3c : word) = Some W_4ae3c.
Proof. vm_refl. Qed.
Lemma D_4ae3c : decode_any W_4ae3c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae40 : bv 32 := 0x00913423.
Lemma F_4ae40 : fetch_word Plain.M.loaded_segments (0x4ae40 : word) = Some W_4ae40.
Proof. vm_refl. Qed.
Lemma D_4ae40 : decode_any W_4ae40 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae44 : bv 32 := 0x01213023.
Lemma F_4ae44 : fetch_word Plain.M.loaded_segments (0x4ae44 : word) = Some W_4ae44.
Proof. vm_refl. Qed.
Lemma D_4ae44 : decode_any W_4ae44 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae48 : bv 32 := 0x00060413.
Lemma F_4ae48 : fetch_word Plain.M.loaded_segments (0x4ae48 : word) = Some W_4ae48.
Proof. vm_refl. Qed.
Lemma D_4ae48 : decode_any W_4ae48 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae4c : bv 32 := 0x00058493.
Lemma F_4ae4c : fetch_word Plain.M.loaded_segments (0x4ae4c : word) = Some W_4ae4c.
Proof. vm_refl. Qed.
Lemma D_4ae4c : decode_any W_4ae4c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae50 : bv 32 := 0x00050913.
Lemma F_4ae50 : fetch_word Plain.M.loaded_segments (0x4ae50 : word) = Some W_4ae50.
Proof. vm_refl. Qed.
Lemma D_4ae50 : decode_any W_4ae50 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae54 : bv 32 := 0x00063583.
Lemma F_4ae54 : fetch_word Plain.M.loaded_segments (0x4ae54 : word) = Some W_4ae54.
Proof. vm_refl. Qed.
Lemma D_4ae54 : decode_any W_4ae54 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae58 : bv 32 := 0x00349513.
Lemma F_4ae58 : fetch_word Plain.M.loaded_segments (0x4ae58 : word) = Some W_4ae58.
Proof. vm_refl. Qed.
Lemma D_4ae58 : decode_any W_4ae58 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae5c : bv 32 := 0x00a60533.
Lemma F_4ae5c : fetch_word Plain.M.loaded_segments (0x4ae5c : word) = Some W_4ae5c.
Proof. vm_refl. Qed.
Lemma D_4ae5c : decode_any W_4ae5c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae60 : bv 32 := 0x00850513.
Lemma F_4ae60 : fetch_word Plain.M.loaded_segments (0x4ae60 : word) = Some W_4ae60.
Proof. vm_refl. Qed.
Lemma D_4ae60 : decode_any W_4ae60 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae64 : bv 32 := 0xd59ff0ef.
Lemma F_4ae64 : fetch_word Plain.M.loaded_segments (0x4ae64 : word) = Some W_4ae64.
Proof. vm_refl. Qed.
Lemma D_4ae64 : decode_any W_4ae64 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae68 : bv 32 := 0x00000517.
Lemma F_4ae68 : fetch_word Plain.M.loaded_segments (0x4ae68 : word) = Some W_4ae68.
Proof. vm_refl. Qed.
Lemma D_4ae68 : decode_any W_4ae68 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae6c : bv 32 := 0x02c50313.
Lemma F_4ae6c : fetch_word Plain.M.loaded_segments (0x4ae6c : word) = Some W_4ae6c.
Proof. vm_refl. Qed.
Lemma D_4ae6c : decode_any W_4ae6c = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae70 : bv 32 := 0x00090513.
Lemma F_4ae70 : fetch_word Plain.M.loaded_segments (0x4ae70 : word) = Some W_4ae70.
Proof. vm_refl. Qed.
Lemma D_4ae70 : decode_any W_4ae70 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae74 : bv 32 := 0x00048593.
Lemma F_4ae74 : fetch_word Plain.M.loaded_segments (0x4ae74 : word) = Some W_4ae74.
Proof. vm_refl. Qed.
Lemma D_4ae74 : decode_any W_4ae74 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae78 : bv 32 := 0x00040613.
Lemma F_4ae78 : fetch_word Plain.M.loaded_segments (0x4ae78 : word) = Some W_4ae78.
Proof. vm_refl. Qed.
Lemma D_4ae78 : decode_any W_4ae78 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae7c : bv 32 := 0x01813083.
Lemma F_4ae7c : fetch_word Plain.M.loaded_segments (0x4ae7c : word) = Some W_4ae7c.
Proof. vm_refl. Qed.
Lemma D_4ae7c : decode_any W_4ae7c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae80 : bv 32 := 0x01013403.
Lemma F_4ae80 : fetch_word Plain.M.loaded_segments (0x4ae80 : word) = Some W_4ae80.
Proof. vm_refl. Qed.
Lemma D_4ae80 : decode_any W_4ae80 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae84 : bv 32 := 0x00813483.
Lemma F_4ae84 : fetch_word Plain.M.loaded_segments (0x4ae84 : word) = Some W_4ae84.
Proof. vm_refl. Qed.
Lemma D_4ae84 : decode_any W_4ae84 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae88 : bv 32 := 0x00013903.
Lemma F_4ae88 : fetch_word Plain.M.loaded_segments (0x4ae88 : word) = Some W_4ae88.
Proof. vm_refl. Qed.
Lemma D_4ae88 : decode_any W_4ae88 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae8c : bv 32 := 0x02010113.
Lemma F_4ae8c : fetch_word Plain.M.loaded_segments (0x4ae8c : word) = Some W_4ae8c.
Proof. vm_refl. Qed.
Lemma D_4ae8c : decode_any W_4ae8c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae90 : bv 32 := 0x00030067.
Lemma F_4ae90 : fetch_word Plain.M.loaded_segments (0x4ae90 : word) = Some W_4ae90.
Proof. vm_refl. Qed.
Lemma D_4ae90 : decode_any W_4ae90 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae94 : bv 32 := 0xfd010113.
Lemma F_4ae94 : fetch_word Plain.M.loaded_segments (0x4ae94 : word) = Some W_4ae94.
Proof. vm_refl. Qed.
Lemma D_4ae94 : decode_any W_4ae94 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae98 : bv 32 := 0x02113423.
Lemma F_4ae98 : fetch_word Plain.M.loaded_segments (0x4ae98 : word) = Some W_4ae98.
Proof. vm_refl. Qed.
Lemma D_4ae98 : decode_any W_4ae98 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ae9c : bv 32 := 0x02813023.
Lemma F_4ae9c : fetch_word Plain.M.loaded_segments (0x4ae9c : word) = Some W_4ae9c.
Proof. vm_refl. Qed.
Lemma D_4ae9c : decode_any W_4ae9c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aea0 : bv 32 := 0x00913c23.
Lemma F_4aea0 : fetch_word Plain.M.loaded_segments (0x4aea0 : word) = Some W_4aea0.
Proof. vm_refl. Qed.
Lemma D_4aea0 : decode_any W_4aea0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aea4 : bv 32 := 0x01213823.
Lemma F_4aea4 : fetch_word Plain.M.loaded_segments (0x4aea4 : word) = Some W_4aea4.
Proof. vm_refl. Qed.
Lemma D_4aea4 : decode_any W_4aea4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aea8 : bv 32 := 0x01313423.
Lemma F_4aea8 : fetch_word Plain.M.loaded_segments (0x4aea8 : word) = Some W_4aea8.
Proof. vm_refl. Qed.
Lemma D_4aea8 : decode_any W_4aea8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aeac : bv 32 := 0x00060413.
Lemma F_4aeac : fetch_word Plain.M.loaded_segments (0x4aeac : word) = Some W_4aeac.
Proof. vm_refl. Qed.
Lemma D_4aeac : decode_any W_4aeac = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aeb0 : bv 32 := 0x00058493.
Lemma F_4aeb0 : fetch_word Plain.M.loaded_segments (0x4aeb0 : word) = Some W_4aeb0.
Proof. vm_refl. Qed.
Lemma D_4aeb0 : decode_any W_4aeb0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aeb4 : bv 32 := 0x00050913.
Lemma F_4aeb4 : fetch_word Plain.M.loaded_segments (0x4aeb4 : word) = Some W_4aeb4.
Proof. vm_refl. Qed.
Lemma D_4aeb4 : decode_any W_4aeb4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aeb8 : bv 32 := 0x00359513.
Lemma F_4aeb8 : fetch_word Plain.M.loaded_segments (0x4aeb8 : word) = Some W_4aeb8.
Proof. vm_refl. Qed.
Lemma D_4aeb8 : decode_any W_4aeb8 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aebc : bv 32 := 0x00a60533.
Lemma F_4aebc : fetch_word Plain.M.loaded_segments (0x4aebc : word) = Some W_4aebc.
Proof. vm_refl. Qed.
Lemma D_4aebc : decode_any W_4aebc = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aec0 : bv 32 := 0x00850993.
Lemma F_4aec0 : fetch_word Plain.M.loaded_segments (0x4aec0 : word) = Some W_4aec0.
Proof. vm_refl. Qed.
Lemma D_4aec0 : decode_any W_4aec0 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aec4 : bv 32 := 0xf25ff0ef.
Lemma F_4aec4 : fetch_word Plain.M.loaded_segments (0x4aec4 : word) = Some W_4aec4.
Proof. vm_refl. Qed.
Lemma D_4aec4 : decode_any W_4aec4 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aec8 : bv 32 := 0x00048513.
Lemma F_4aec8 : fetch_word Plain.M.loaded_segments (0x4aec8 : word) = Some W_4aec8.
Proof. vm_refl. Qed.
Lemma D_4aec8 : decode_any W_4aec8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aecc : bv 32 := 0x00040593.
Lemma F_4aecc : fetch_word Plain.M.loaded_segments (0x4aecc : word) = Some W_4aecc.
Proof. vm_refl. Qed.
Lemma D_4aecc : decode_any W_4aecc = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aed0 : bv 32 := 0x00098613.
Lemma F_4aed0 : fetch_word Plain.M.loaded_segments (0x4aed0 : word) = Some W_4aed0.
Proof. vm_refl. Qed.
Lemma D_4aed0 : decode_any W_4aed0 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aed4 : bv 32 := 0x000900e7.
Lemma F_4aed4 : fetch_word Plain.M.loaded_segments (0x4aed4 : word) = Some W_4aed4.
Proof. vm_refl. Qed.
Lemma D_4aed4 : decode_any W_4aed4 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aedc : bv 32 := 0xfc010113.
Lemma F_4aedc : fetch_word Plain.M.loaded_segments (0x4aedc : word) = Some W_4aedc.
Proof. vm_refl. Qed.
Lemma D_4aedc : decode_any W_4aedc = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aee0 : bv 32 := 0x02113c23.
Lemma F_4aee0 : fetch_word Plain.M.loaded_segments (0x4aee0 : word) = Some W_4aee0.
Proof. vm_refl. Qed.
Lemma D_4aee0 : decode_any W_4aee0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aee4 : bv 32 := 0x02813823.
Lemma F_4aee4 : fetch_word Plain.M.loaded_segments (0x4aee4 : word) = Some W_4aee4.
Proof. vm_refl. Qed.
Lemma D_4aee4 : decode_any W_4aee4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aee8 : bv 32 := 0x02913423.
Lemma F_4aee8 : fetch_word Plain.M.loaded_segments (0x4aee8 : word) = Some W_4aee8.
Proof. vm_refl. Qed.
Lemma D_4aee8 : decode_any W_4aee8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aeec : bv 32 := 0x03213023.
Lemma F_4aeec : fetch_word Plain.M.loaded_segments (0x4aeec : word) = Some W_4aeec.
Proof. vm_refl. Qed.
Lemma D_4aeec : decode_any W_4aeec = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aef0 : bv 32 := 0x01313c23.
Lemma F_4aef0 : fetch_word Plain.M.loaded_segments (0x4aef0 : word) = Some W_4aef0.
Proof. vm_refl. Qed.
Lemma D_4aef0 : decode_any W_4aef0 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aef4 : bv 32 := 0x01413823.
Lemma F_4aef4 : fetch_word Plain.M.loaded_segments (0x4aef4 : word) = Some W_4aef4.
Proof. vm_refl. Qed.
Lemma D_4aef4 : decode_any W_4aef4 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aef8 : bv 32 := 0x01513423.
Lemma F_4aef8 : fetch_word Plain.M.loaded_segments (0x4aef8 : word) = Some W_4aef8.
Proof. vm_refl. Qed.
Lemma D_4aef8 : decode_any W_4aef8 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4aefc : bv 32 := 0x02853683.
Lemma F_4aefc : fetch_word Plain.M.loaded_segments (0x4aefc : word) = Some W_4aefc.
Proof. vm_refl. Qed.
Lemma D_4aefc : decode_any W_4aefc = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af00 : bv 32 := 0x00045597.
Lemma F_4af00 : fetch_word Plain.M.loaded_segments (0x4af00 : word) = Some W_4af00.
Proof. vm_refl. Qed.
Lemma D_4af00 : decode_any W_4af00 = Some (Auipc 11 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af10 : bv 32 := 0x0c068e63.
Lemma F_4af10 : fetch_word Plain.M.loaded_segments (0x4af10 : word) = Some W_4af10.
Proof. vm_refl. Qed.
Lemma D_4af10 : decode_any W_4af10 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af18 : bv 32 := 0x00000893.
Lemma F_4af18 : fetch_word Plain.M.loaded_segments (0x4af18 : word) = Some W_4af18.
Proof. vm_refl. Qed.
Lemma D_4af18 : decode_any W_4af18 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af1c : bv 32 := 0x00015717.
Lemma F_4af1c : fetch_word Plain.M.loaded_segments (0x4af1c : word) = Some W_4af1c.
Proof. vm_refl. Qed.
Lemma D_4af1c : decode_any W_4af1c = Some (Auipc 14 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af20 : bv 32 := 0x01853783.
Lemma F_4af20 : fetch_word Plain.M.loaded_segments (0x4af20 : word) = Some W_4af20.
Proof. vm_refl. Qed.
Lemma D_4af20 : decode_any W_4af20 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af24 : bv 32 := 0x02053503.
Lemma F_4af24 : fetch_word Plain.M.loaded_segments (0x4af24 : word) = Some W_4af24.
Proof. vm_refl. Qed.
Lemma D_4af24 : decode_any W_4af24 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af28 : bv 32 := 0x00600813.
Lemma F_4af28 : fetch_word Plain.M.loaded_segments (0x4af28 : word) = Some W_4af28.
Proof. vm_refl. Qed.
Lemma D_4af28 : decode_any W_4af28 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af2c : bv 32 := 0x00013297.
Lemma F_4af2c : fetch_word Plain.M.loaded_segments (0x4af2c : word) = Some W_4af2c.
Proof. vm_refl. Qed.
Lemma D_4af2c : decode_any W_4af2c = Some (Auipc 5 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af30 : bv 32 := 0x94476f03.
Lemma F_4af30 : fetch_word Plain.M.loaded_segments (0x4af30 : word) = Some W_4af30.
Proof. vm_refl. Qed.
Lemma D_4af30 : decode_any W_4af30 = Some (Load SZ4 false 30 14 2372, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af34 : bv 32 := 0x5742b283.
Lemma F_4af34 : fetch_word Plain.M.loaded_segments (0x4af34 : word) = Some W_4af34.
Proof. vm_refl. Qed.
Lemma D_4af34 : decode_any W_4af34 = Some (Load SZ8 true 5 5 1396, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af38 : bv 32 := 0x00200313.
Lemma F_4af38 : fetch_word Plain.M.loaded_segments (0x4af38 : word) = Some W_4af38.
Proof. vm_refl. Qed.
Lemma D_4af38 : decode_any W_4af38 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af3c : bv 32 := 0x00700393.
Lemma F_4af3c : fetch_word Plain.M.loaded_segments (0x4af3c : word) = Some W_4af3c.
Proof. vm_refl. Qed.
Lemma D_4af3c : decode_any W_4af3c = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af40 : bv 32 := 0x6474ee37.
Lemma F_4af40 : fetch_word Plain.M.loaded_segments (0x4af40 : word) = Some W_4af40.
Proof. vm_refl. Qed.
Lemma D_4af40 : decode_any W_4af40 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af44 : bv 32 := 0x551e0e1b.
Lemma F_4af44 : fetch_word Plain.M.loaded_segments (0x4af44 : word) = Some W_4af44.
Proof. vm_refl. Qed.
Lemma D_4af44 : decode_any W_4af44 = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af48 : bv 32 := 0x00078e93.
Lemma F_4af48 : fetch_word Plain.M.loaded_segments (0x4af48 : word) = Some W_4af48.
Proof. vm_refl. Qed.
Lemma D_4af48 : decode_any W_4af48 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af4c : bv 32 := 0x0180006f.
Lemma F_4af4c : fetch_word Plain.M.loaded_segments (0x4af4c : word) = Some W_4af4c.
Proof. vm_refl. Qed.
Lemma D_4af4c : decode_any W_4af4c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af58 : bv 32 := 0xfff68693.
Lemma F_4af58 : fetch_word Plain.M.loaded_segments (0x4af58 : word) = Some W_4af58.
Proof. vm_refl. Qed.
Lemma D_4af58 : decode_any W_4af58 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af5c : bv 32 := 0x00ae8eb3.
Lemma F_4af5c : fetch_word Plain.M.loaded_segments (0x4af5c : word) = Some W_4af5c.
Proof. vm_refl. Qed.
Lemma D_4af5c : decode_any W_4af5c = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af60 : bv 32 := 0x04068a63.
Lemma F_4af60 : fetch_word Plain.M.loaded_segments (0x4af60 : word) = Some W_4af60.
Proof. vm_refl. Qed.
Lemma D_4af60 : decode_any W_4af60 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af64 : bv 32 := 0x000ea403.
Lemma F_4af64 : fetch_word Plain.M.loaded_segments (0x4af64 : word) = Some W_4af64.
Proof. vm_refl. Qed.
Lemma D_4af64 : decode_any W_4af64 = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af68 : bv 32 := 0xff0404e3.
Lemma F_4af68 : fetch_word Plain.M.loaded_segments (0x4af68 : word) = Some W_4af68.
Proof. vm_refl. Qed.
Lemma D_4af68 : decode_any W_4af68 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af6c : bv 32 := 0x00028a63.
Lemma F_4af6c : fetch_word Plain.M.loaded_segments (0x4af6c : word) = Some W_4af6c.
Proof. vm_refl. Qed.
Lemma D_4af6c : decode_any W_4af6c = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af80 : bv 32 := 0x000e8f93.
Lemma F_4af80 : fetch_word Plain.M.loaded_segments (0x4af80 : word) = Some W_4af80.
Proof. vm_refl. Qed.
Lemma D_4af80 : decode_any W_4af80 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af84 : bv 32 := 0x00740463.
Lemma F_4af84 : fetch_word Plain.M.loaded_segments (0x4af84 : word) = Some W_4af84.
Proof. vm_refl. Qed.
Lemma D_4af84 : decode_any W_4af84 = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af88 : bv 32 := 0x00088f93.
Lemma F_4af88 : fetch_word Plain.M.loaded_segments (0x4af88 : word) = Some W_4af88.
Proof. vm_refl. Qed.
Lemma D_4af88 : decode_any W_4af88 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af8c : bv 32 := 0x03c41063.
Lemma F_4af8c : fetch_word Plain.M.loaded_segments (0x4af8c : word) = Some W_4af8c.
Proof. vm_refl. Qed.
Lemma D_4af8c : decode_any W_4af8c = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af90 : bv 32 := 0x028eb883.
Lemma F_4af90 : fetch_word Plain.M.loaded_segments (0x4af90 : word) = Some W_4af90.
Proof. vm_refl. Qed.
Lemma D_4af90 : decode_any W_4af90 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4af94 : bv 32 := 0x011f7c63.
Lemma F_4af94 : fetch_word Plain.M.loaded_segments (0x4af94 : word) = Some W_4af94.
Proof. vm_refl. Qed.
Lemma D_4af94 : decode_any W_4af94 = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4afac : bv 32 := 0x000f8893.
Lemma F_4afac : fetch_word Plain.M.loaded_segments (0x4afac : word) = Some W_4afac.
Proof. vm_refl. Qed.
Lemma D_4afac : decode_any W_4afac = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4afb0 : bv 32 := 0xfa9ff06f.
Lemma F_4afb0 : fetch_word Plain.M.loaded_segments (0x4afb0 : word) = Some W_4afb0.
Proof. vm_refl. Qed.
Lemma D_4afb0 : decode_any W_4afb0 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4afb4 : bv 32 := 0x02088c63.
Lemma F_4afb4 : fetch_word Plain.M.loaded_segments (0x4afb4 : word) = Some W_4afb4.
Proof. vm_refl. Qed.
Lemma D_4afb4 : decode_any W_4afb4 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4affc : bv 32 := 0xfff50793.
Lemma F_4affc : fetch_word Plain.M.loaded_segments (0x4affc : word) = Some W_4affc.
Proof. vm_refl. Qed.
Lemma D_4affc : decode_any W_4affc = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b000 : bv 32 := 0x40e00733.
Lemma F_4b000 : fetch_word Plain.M.loaded_segments (0x4b000 : word) = Some W_4b000.
Proof. vm_refl. Qed.
Lemma D_4b000 : decode_any W_4b000 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b008 : bv 32 := 0x00e7f733.
Lemma F_4b008 : fetch_word Plain.M.loaded_segments (0x4b008 : word) = Some W_4b008.
Proof. vm_refl. Qed.
Lemma D_4b008 : decode_any W_4b008 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b00c : bv 32 := 0x00700793.
Lemma F_4b00c : fetch_word Plain.M.loaded_segments (0x4b00c : word) = Some W_4b00c.
Proof. vm_refl. Qed.
Lemma D_4b00c : decode_any W_4b00c = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b010 : bv 32 := 0x00d706b3.
Lemma F_4b010 : fetch_word Plain.M.loaded_segments (0x4b010 : word) = Some W_4b010.
Proof. vm_refl. Qed.
Lemma D_4b010 : decode_any W_4b010 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b01c : bv 32 := 0x00a7e663.
Lemma F_4b01c : fetch_word Plain.M.loaded_segments (0x4b01c : word) = Some W_4b01c.
Proof. vm_refl. Qed.
Lemma D_4b01c : decode_any W_4b01c = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b020 : bv 32 := 0x00800513.
Lemma F_4b020 : fetch_word Plain.M.loaded_segments (0x4b020 : word) = Some W_4b020.
Proof. vm_refl. Qed.
Lemma D_4b020 : decode_any W_4b020 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b03c : bv 32 := 0xff85f593.
Lemma F_4b03c : fetch_word Plain.M.loaded_segments (0x4b03c : word) = Some W_4b03c.
Proof. vm_refl. Qed.
Lemma D_4b03c : decode_any W_4b03c = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b040 : bv 32 := 0x00b4bc23.
Lemma F_4b040 : fetch_word Plain.M.loaded_segments (0x4b040 : word) = Some W_4b040.
Proof. vm_refl. Qed.
Lemma D_4b040 : decode_any W_4b040 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b044 : bv 32 := 0x02a4b023.
Lemma F_4b044 : fetch_word Plain.M.loaded_segments (0x4b044 : word) = Some W_4b044.
Proof. vm_refl. Qed.
Lemma D_4b044 : decode_any W_4b044 = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b048 : bv 32 := 0x02d5ea63.
Lemma F_4b048 : fetch_word Plain.M.loaded_segments (0x4b048 : word) = Some W_4b048.
Proof. vm_refl. Qed.
Lemma D_4b048 : decode_any W_4b048 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b084 : bv 32 := 0x0284b603.
Lemma F_4b084 : fetch_word Plain.M.loaded_segments (0x4b084 : word) = Some W_4b084.
Proof. vm_refl. Qed.
Lemma D_4b084 : decode_any W_4b084 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b0b0 : bv 32 := 0x0c890413.
Lemma F_4b0b0 : fetch_word Plain.M.loaded_segments (0x4b0b0 : word) = Some W_4b0b0.
Proof. vm_refl. Qed.
Lemma D_4b0b0 : decode_any W_4b0b0 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.
