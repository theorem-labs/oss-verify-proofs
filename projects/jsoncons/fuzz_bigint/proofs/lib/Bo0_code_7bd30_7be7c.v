(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7bd30 : bv 32 := 0xfe010113.
Lemma F_7bd30 : fetch_word AsanUbsan.M.loaded_segments (0x7bd30 : word) = Some W_7bd30.
Proof. vm_refl. Qed.
Lemma D_7bd30 : decode_any W_7bd30 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd34 : bv 32 := 0x00113c23.
Lemma F_7bd34 : fetch_word AsanUbsan.M.loaded_segments (0x7bd34 : word) = Some W_7bd34.
Proof. vm_refl. Qed.
Lemma D_7bd34 : decode_any W_7bd34 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd38 : bv 32 := 0x00813823.
Lemma F_7bd38 : fetch_word AsanUbsan.M.loaded_segments (0x7bd38 : word) = Some W_7bd38.
Proof. vm_refl. Qed.
Lemma D_7bd38 : decode_any W_7bd38 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd3c : bv 32 := 0x00913423.
Lemma F_7bd3c : fetch_word AsanUbsan.M.loaded_segments (0x7bd3c : word) = Some W_7bd3c.
Proof. vm_refl. Qed.
Lemma D_7bd3c : decode_any W_7bd3c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd40 : bv 32 := 0x01213023.
Lemma F_7bd40 : fetch_word AsanUbsan.M.loaded_segments (0x7bd40 : word) = Some W_7bd40.
Proof. vm_refl. Qed.
Lemma D_7bd40 : decode_any W_7bd40 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd44 : bv 32 := 0x00060413.
Lemma F_7bd44 : fetch_word AsanUbsan.M.loaded_segments (0x7bd44 : word) = Some W_7bd44.
Proof. vm_refl. Qed.
Lemma D_7bd44 : decode_any W_7bd44 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd48 : bv 32 := 0x00058493.
Lemma F_7bd48 : fetch_word AsanUbsan.M.loaded_segments (0x7bd48 : word) = Some W_7bd48.
Proof. vm_refl. Qed.
Lemma D_7bd48 : decode_any W_7bd48 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd4c : bv 32 := 0x00058513.
Lemma F_7bd4c : fetch_word AsanUbsan.M.loaded_segments (0x7bd4c : word) = Some W_7bd4c.
Proof. vm_refl. Qed.
Lemma D_7bd4c : decode_any W_7bd4c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd50 : bv 32 := 0x00060593.
Lemma F_7bd50 : fetch_word AsanUbsan.M.loaded_segments (0x7bd50 : word) = Some W_7bd50.
Proof. vm_refl. Qed.
Lemma D_7bd50 : decode_any W_7bd50 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd54 : bv 32 := 0x00068613.
Lemma F_7bd54 : fetch_word AsanUbsan.M.loaded_segments (0x7bd54 : word) = Some W_7bd54.
Proof. vm_refl. Qed.
Lemma D_7bd54 : decode_any W_7bd54 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd58 : bv 32 := 0xf19f70ef.
Lemma F_7bd58 : fetch_word AsanUbsan.M.loaded_segments (0x7bd58 : word) = Some W_7bd58.
Proof. vm_refl. Qed.
Lemma D_7bd58 : decode_any W_7bd58 = Some (Jal 1 2064152, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd5c : bv 32 := 0x00050e63.
Lemma F_7bd5c : fetch_word AsanUbsan.M.loaded_segments (0x7bd5c : word) = Some W_7bd5c.
Proof. vm_refl. Qed.
Lemma D_7bd5c : decode_any W_7bd5c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd60 : bv 32 := 0x01813083.
Lemma F_7bd60 : fetch_word AsanUbsan.M.loaded_segments (0x7bd60 : word) = Some W_7bd60.
Proof. vm_refl. Qed.
Lemma D_7bd60 : decode_any W_7bd60 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd64 : bv 32 := 0x01013403.
Lemma F_7bd64 : fetch_word AsanUbsan.M.loaded_segments (0x7bd64 : word) = Some W_7bd64.
Proof. vm_refl. Qed.
Lemma D_7bd64 : decode_any W_7bd64 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd68 : bv 32 := 0x00813483.
Lemma F_7bd68 : fetch_word AsanUbsan.M.loaded_segments (0x7bd68 : word) = Some W_7bd68.
Proof. vm_refl. Qed.
Lemma D_7bd68 : decode_any W_7bd68 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd6c : bv 32 := 0x00013903.
Lemma F_7bd6c : fetch_word AsanUbsan.M.loaded_segments (0x7bd6c : word) = Some W_7bd6c.
Proof. vm_refl. Qed.
Lemma D_7bd6c : decode_any W_7bd6c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd70 : bv 32 := 0x02010113.
Lemma F_7bd70 : fetch_word AsanUbsan.M.loaded_segments (0x7bd70 : word) = Some W_7bd70.
Proof. vm_refl. Qed.
Lemma D_7bd70 : decode_any W_7bd70 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd74 : bv 32 := 0x00008067.
Lemma F_7bd74 : fetch_word AsanUbsan.M.loaded_segments (0x7bd74 : word) = Some W_7bd74.
Proof. vm_refl. Qed.
Lemma D_7bd74 : decode_any W_7bd74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd78 : bv 32 := 0x00050913.
Lemma F_7bd78 : fetch_word AsanUbsan.M.loaded_segments (0x7bd78 : word) = Some W_7bd78.
Proof. vm_refl. Qed.
Lemma D_7bd78 : decode_any W_7bd78 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd7c : bv 32 := 0x00048513.
Lemma F_7bd7c : fetch_word AsanUbsan.M.loaded_segments (0x7bd7c : word) = Some W_7bd7c.
Proof. vm_refl. Qed.
Lemma D_7bd7c : decode_any W_7bd7c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd80 : bv 32 := 0x00040593.
Lemma F_7bd80 : fetch_word AsanUbsan.M.loaded_segments (0x7bd80 : word) = Some W_7bd80.
Proof. vm_refl. Qed.
Lemma D_7bd80 : decode_any W_7bd80 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd84 : bv 32 := 0x020000ef.
Lemma F_7bd84 : fetch_word AsanUbsan.M.loaded_segments (0x7bd84 : word) = Some W_7bd84.
Proof. vm_refl. Qed.
Lemma D_7bd84 : decode_any W_7bd84 = Some (Jal 1 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd88 : bv 32 := 0x00090513.
Lemma F_7bd88 : fetch_word AsanUbsan.M.loaded_segments (0x7bd88 : word) = Some W_7bd88.
Proof. vm_refl. Qed.
Lemma D_7bd88 : decode_any W_7bd88 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd8c : bv 32 := 0x01813083.
Lemma F_7bd8c : fetch_word AsanUbsan.M.loaded_segments (0x7bd8c : word) = Some W_7bd8c.
Proof. vm_refl. Qed.
Lemma D_7bd8c : decode_any W_7bd8c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd90 : bv 32 := 0x01013403.
Lemma F_7bd90 : fetch_word AsanUbsan.M.loaded_segments (0x7bd90 : word) = Some W_7bd90.
Proof. vm_refl. Qed.
Lemma D_7bd90 : decode_any W_7bd90 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd94 : bv 32 := 0x00813483.
Lemma F_7bd94 : fetch_word AsanUbsan.M.loaded_segments (0x7bd94 : word) = Some W_7bd94.
Proof. vm_refl. Qed.
Lemma D_7bd94 : decode_any W_7bd94 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd98 : bv 32 := 0x00013903.
Lemma F_7bd98 : fetch_word AsanUbsan.M.loaded_segments (0x7bd98 : word) = Some W_7bd98.
Proof. vm_refl. Qed.
Lemma D_7bd98 : decode_any W_7bd98 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd9c : bv 32 := 0x02010113.
Lemma F_7bd9c : fetch_word AsanUbsan.M.loaded_segments (0x7bd9c : word) = Some W_7bd9c.
Proof. vm_refl. Qed.
Lemma D_7bd9c : decode_any W_7bd9c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bda0 : bv 32 := 0x00008067.
Lemma F_7bda0 : fetch_word AsanUbsan.M.loaded_segments (0x7bda0 : word) = Some W_7bda0.
Proof. vm_refl. Qed.
Lemma D_7bda0 : decode_any W_7bda0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bda4 : bv 32 := 0xfe010113.
Lemma F_7bda4 : fetch_word AsanUbsan.M.loaded_segments (0x7bda4 : word) = Some W_7bda4.
Proof. vm_refl. Qed.
Lemma D_7bda4 : decode_any W_7bda4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bda8 : bv 32 := 0x00113c23.
Lemma F_7bda8 : fetch_word AsanUbsan.M.loaded_segments (0x7bda8 : word) = Some W_7bda8.
Proof. vm_refl. Qed.
Lemma D_7bda8 : decode_any W_7bda8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdac : bv 32 := 0x00813823.
Lemma F_7bdac : fetch_word AsanUbsan.M.loaded_segments (0x7bdac : word) = Some W_7bdac.
Proof. vm_refl. Qed.
Lemma D_7bdac : decode_any W_7bdac = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdb0 : bv 32 := 0x00913423.
Lemma F_7bdb0 : fetch_word AsanUbsan.M.loaded_segments (0x7bdb0 : word) = Some W_7bdb0.
Proof. vm_refl. Qed.
Lemma D_7bdb0 : decode_any W_7bdb0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdb4 : bv 32 := 0x01213023.
Lemma F_7bdb4 : fetch_word AsanUbsan.M.loaded_segments (0x7bdb4 : word) = Some W_7bdb4.
Proof. vm_refl. Qed.
Lemma D_7bdb4 : decode_any W_7bdb4 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdb8 : bv 32 := 0x0005a617.
Lemma F_7bdb8 : fetch_word AsanUbsan.M.loaded_segments (0x7bdb8 : word) = Some W_7bdb8.
Proof. vm_refl. Qed.
Lemma D_7bdb8 : decode_any W_7bdb8 = Some (Auipc 12 90, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdbc : bv 32 := 0x75063603.
Lemma F_7bdbc : fetch_word AsanUbsan.M.loaded_segments (0x7bdbc : word) = Some W_7bdbc.
Proof. vm_refl. Qed.
Lemma D_7bdbc : decode_any W_7bdbc = Some (Load SZ8 true 12 12 1872, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdc0 : bv 32 := 0x06060e63.
Lemma F_7bdc0 : fetch_word AsanUbsan.M.loaded_segments (0x7bdc0 : word) = Some W_7bdc0.
Proof. vm_refl. Qed.
Lemma D_7bdc0 : decode_any W_7bdc0 = Some (Branch BC_EQ 12 0 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdc4 : bv 32 := 0x00050413.
Lemma F_7bdc4 : fetch_word AsanUbsan.M.loaded_segments (0x7bdc4 : word) = Some W_7bdc4.
Proof. vm_refl. Qed.
Lemma D_7bdc4 : decode_any W_7bdc4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdc8 : bv 32 := 0x0005a517.
Lemma F_7bdc8 : fetch_word AsanUbsan.M.loaded_segments (0x7bdc8 : word) = Some W_7bdc8.
Proof. vm_refl. Qed.
Lemma D_7bdc8 : decode_any W_7bdc8 = Some (Auipc 10 90, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdcc : bv 32 := 0x6e053903.
Lemma F_7bdcc : fetch_word AsanUbsan.M.loaded_segments (0x7bdcc : word) = Some W_7bdcc.
Proof. vm_refl. Qed.
Lemma D_7bdcc : decode_any W_7bdcc = Some (Load SZ8 true 18 10 1760, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdd0 : bv 32 := 0x00093503.
Lemma F_7bdd0 : fetch_word AsanUbsan.M.loaded_segments (0x7bdd0 : word) = Some W_7bdd0.
Proof. vm_refl. Qed.
Lemma D_7bdd0 : decode_any W_7bdd0 = Some (Load SZ8 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdd4 : bv 32 := 0x00051a63.
Lemma F_7bdd4 : fetch_word AsanUbsan.M.loaded_segments (0x7bdd4 : word) = Some W_7bdd4.
Proof. vm_refl. Qed.
Lemma D_7bdd4 : decode_any W_7bdd4 = Some (Branch BC_NE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdd8 : bv 32 := 0x00058493.
Lemma F_7bdd8 : fetch_word AsanUbsan.M.loaded_segments (0x7bdd8 : word) = Some W_7bdd8.
Proof. vm_refl. Qed.
Lemma D_7bdd8 : decode_any W_7bdd8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bddc : bv 32 := 0xf31f60ef.
Lemma F_7bddc : fetch_word AsanUbsan.M.loaded_segments (0x7bddc : word) = Some W_7bddc.
Proof. vm_refl. Qed.
Lemma D_7bddc : decode_any W_7bddc = Some (Jal 1 2060080, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bde0 : bv 32 := 0x00048593.
Lemma F_7bde0 : fetch_word AsanUbsan.M.loaded_segments (0x7bde0 : word) = Some W_7bde0.
Proof. vm_refl. Qed.
Lemma D_7bde0 : decode_any W_7bde0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bde4 : bv 32 := 0x00a93023.
Lemma F_7bde4 : fetch_word AsanUbsan.M.loaded_segments (0x7bde4 : word) = Some W_7bde4.
Proof. vm_refl. Qed.
Lemma D_7bde4 : decode_any W_7bde4 = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bde8 : bv 32 := 0xfff50613.
Lemma F_7bde8 : fetch_word AsanUbsan.M.loaded_segments (0x7bde8 : word) = Some W_7bde8.
Proof. vm_refl. Qed.
Lemma D_7bde8 : decode_any W_7bde8 = Some (OpImm ALU_ADD 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdec : bv 32 := 0x00c57633.
Lemma F_7bdec : fetch_word AsanUbsan.M.loaded_segments (0x7bdec : word) = Some W_7bdec.
Proof. vm_refl. Qed.
Lemma D_7bdec : decode_any W_7bdec = Some (Op ALU_AND 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdf0 : bv 32 := 0x06061c63.
Lemma F_7bdf0 : fetch_word AsanUbsan.M.loaded_segments (0x7bdf0 : word) = Some W_7bdf0.
Proof. vm_refl. Qed.
Lemma D_7bdf0 : decode_any W_7bdf0 = Some (Branch BC_NE 12 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdf4 : bv 32 := 0x00a585b3.
Lemma F_7bdf4 : fetch_word AsanUbsan.M.loaded_segments (0x7bdf4 : word) = Some W_7bdf4.
Proof. vm_refl. Qed.
Lemma D_7bdf4 : decode_any W_7bdf4 = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdf8 : bv 32 := 0xfff58493.
Lemma F_7bdf8 : fetch_word AsanUbsan.M.loaded_segments (0x7bdf8 : word) = Some W_7bdf8.
Proof. vm_refl. Qed.
Lemma D_7bdf8 : decode_any W_7bdf8 = Some (OpImm ALU_ADD 9 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdfc : bv 32 := 0x40a005b3.
Lemma F_7bdfc : fetch_word AsanUbsan.M.loaded_segments (0x7bdfc : word) = Some W_7bdfc.
Proof. vm_refl. Qed.
Lemma D_7bdfc : decode_any W_7bdfc = Some (Op ALU_SUB 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be00 : bv 32 := 0x00b4f4b3.
Lemma F_7be00 : fetch_word AsanUbsan.M.loaded_segments (0x7be00 : word) = Some W_7be00.
Proof. vm_refl. Qed.
Lemma D_7be00 : decode_any W_7be00 = Some (Op ALU_AND 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be04 : bv 32 := 0x00051863.
Lemma F_7be04 : fetch_word AsanUbsan.M.loaded_segments (0x7be04 : word) = Some W_7be04.
Proof. vm_refl. Qed.
Lemma D_7be04 : decode_any W_7be04 = Some (Branch BC_NE 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be08 : bv 32 := 0xf05f60ef.
Lemma F_7be08 : fetch_word AsanUbsan.M.loaded_segments (0x7be08 : word) = Some W_7be08.
Proof. vm_refl. Qed.
Lemma D_7be08 : decode_any W_7be08 = Some (Jal 1 2060036, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be0c : bv 32 := 0x00a93023.
Lemma F_7be0c : fetch_word AsanUbsan.M.loaded_segments (0x7be0c : word) = Some W_7be0c.
Proof. vm_refl. Qed.
Lemma D_7be0c : decode_any W_7be0c = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be10 : bv 32 := 0x40a005b3.
Lemma F_7be10 : fetch_word AsanUbsan.M.loaded_segments (0x7be10 : word) = Some W_7be10.
Proof. vm_refl. Qed.
Lemma D_7be10 : decode_any W_7be10 = Some (Op ALU_SUB 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be14 : bv 32 := 0x00b47433.
Lemma F_7be14 : fetch_word AsanUbsan.M.loaded_segments (0x7be14 : word) = Some W_7be14.
Proof. vm_refl. Qed.
Lemma D_7be14 : decode_any W_7be14 = Some (Op ALU_AND 8 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be18 : bv 32 := 0x00104537.
Lemma F_7be18 : fetch_word AsanUbsan.M.loaded_segments (0x7be18 : word) = Some W_7be18.
Proof. vm_refl. Qed.
Lemma D_7be18 : decode_any W_7be18 = Some (Lui 10 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be1c : bv 32 := 0x0225069b.
Lemma F_7be1c : fetch_word AsanUbsan.M.loaded_segments (0x7be1c : word) = Some W_7be1c.
Proof. vm_refl. Qed.
Lemma D_7be1c : decode_any W_7be1c = Some (OpImm32 13 10 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be20 : bv 32 := 0xfff00713.
Lemma F_7be20 : fetch_word AsanUbsan.M.loaded_segments (0x7be20 : word) = Some W_7be20.
Proof. vm_refl. Qed.
Lemma D_7be20 : decode_any W_7be20 = Some (OpImm ALU_ADD 14 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be24 : bv 32 := 0x00040513.
Lemma F_7be24 : fetch_word AsanUbsan.M.loaded_segments (0x7be24 : word) = Some W_7be24.
Proof. vm_refl. Qed.
Lemma D_7be24 : decode_any W_7be24 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be28 : bv 32 := 0x00048593.
Lemma F_7be28 : fetch_word AsanUbsan.M.loaded_segments (0x7be28 : word) = Some W_7be28.
Proof. vm_refl. Qed.
Lemma D_7be28 : decode_any W_7be28 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be2c : bv 32 := 0x00000613.
Lemma F_7be2c : fetch_word AsanUbsan.M.loaded_segments (0x7be2c : word) = Some W_7be2c.
Proof. vm_refl. Qed.
Lemma D_7be2c : decode_any W_7be2c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be30 : bv 32 := 0x00000793.
Lemma F_7be30 : fetch_word AsanUbsan.M.loaded_segments (0x7be30 : word) = Some W_7be30.
Proof. vm_refl. Qed.
Lemma D_7be30 : decode_any W_7be30 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be34 : bv 32 := 0xfadf50ef.
Lemma F_7be34 : fetch_word AsanUbsan.M.loaded_segments (0x7be34 : word) = Some W_7be34.
Proof. vm_refl. Qed.
Lemma D_7be34 : decode_any W_7be34 = Some (Jal 1 2056108, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be38 : bv 32 := 0x00851e63.
Lemma F_7be38 : fetch_word AsanUbsan.M.loaded_segments (0x7be38 : word) = Some W_7be38.
Proof. vm_refl. Qed.
Lemma D_7be38 : decode_any W_7be38 = Some (Branch BC_NE 10 8 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be3c : bv 32 := 0x01813083.
Lemma F_7be3c : fetch_word AsanUbsan.M.loaded_segments (0x7be3c : word) = Some W_7be3c.
Proof. vm_refl. Qed.
Lemma D_7be3c : decode_any W_7be3c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be40 : bv 32 := 0x01013403.
Lemma F_7be40 : fetch_word AsanUbsan.M.loaded_segments (0x7be40 : word) = Some W_7be40.
Proof. vm_refl. Qed.
Lemma D_7be40 : decode_any W_7be40 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be44 : bv 32 := 0x00813483.
Lemma F_7be44 : fetch_word AsanUbsan.M.loaded_segments (0x7be44 : word) = Some W_7be44.
Proof. vm_refl. Qed.
Lemma D_7be44 : decode_any W_7be44 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be48 : bv 32 := 0x00013903.
Lemma F_7be48 : fetch_word AsanUbsan.M.loaded_segments (0x7be48 : word) = Some W_7be48.
Proof. vm_refl. Qed.
Lemma D_7be48 : decode_any W_7be48 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be4c : bv 32 := 0x02010113.
Lemma F_7be4c : fetch_word AsanUbsan.M.loaded_segments (0x7be4c : word) = Some W_7be4c.
Proof. vm_refl. Qed.
Lemma D_7be4c : decode_any W_7be4c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be50 : bv 32 := 0x00008067.
Lemma F_7be50 : fetch_word AsanUbsan.M.loaded_segments (0x7be50 : word) = Some W_7be50.
Proof. vm_refl. Qed.
Lemma D_7be50 : decode_any W_7be50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be54 : bv 32 := 0x0005a517.
Lemma F_7be54 : fetch_word AsanUbsan.M.loaded_segments (0x7be54 : word) = Some W_7be54.
Proof. vm_refl. Qed.
Lemma D_7be54 : decode_any W_7be54 = Some (Auipc 10 90, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be58 : bv 32 := 0x6bc53503.
Lemma F_7be58 : fetch_word AsanUbsan.M.loaded_segments (0x7be58 : word) = Some W_7be58.
Proof. vm_refl. Qed.
Lemma D_7be58 : decode_any W_7be58 = Some (Load SZ8 true 10 10 1724, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be5c : bv 32 := 0x00052503.
Lemma F_7be5c : fetch_word AsanUbsan.M.loaded_segments (0x7be5c : word) = Some W_7be5c.
Proof. vm_refl. Qed.
Lemma D_7be5c : decode_any W_7be5c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be60 : bv 32 := 0x00051c63.
Lemma F_7be60 : fetch_word AsanUbsan.M.loaded_segments (0x7be60 : word) = Some W_7be60.
Proof. vm_refl. Qed.
Lemma D_7be60 : decode_any W_7be60 = Some (Branch BC_NE 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be64 : bv 32 := 0x0000006f.
Lemma F_7be64 : fetch_word AsanUbsan.M.loaded_segments (0x7be64 : word) = Some W_7be64.
Proof. vm_refl. Qed.
Lemma D_7be64 : decode_any W_7be64 = Some (Jal 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be68 : bv 32 := 0xfff97517.
Lemma F_7be68 : fetch_word AsanUbsan.M.loaded_segments (0x7be68 : word) = Some W_7be68.
Proof. vm_refl. Qed.
Lemma D_7be68 : decode_any W_7be68 = Some (Auipc 10 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be6c : bv 32 := 0x90a50513.
Lemma F_7be6c : fetch_word AsanUbsan.M.loaded_segments (0x7be6c : word) = Some W_7be6c.
Proof. vm_refl. Qed.
Lemma D_7be6c : decode_any W_7be6c = Some (OpImm ALU_ADD 10 10 2314, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be70 : bv 32 := 0xe24f20ef.
Lemma F_7be70 : fetch_word AsanUbsan.M.loaded_segments (0x7be70 : word) = Some W_7be70.
Proof. vm_refl. Qed.
Lemma D_7be70 : decode_any W_7be70 = Some (Jal 1 2041380, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be74 : bv 32 := 0xba8fd0ef.
Lemma F_7be74 : fetch_word AsanUbsan.M.loaded_segments (0x7be74 : word) = Some W_7be74.
Proof. vm_refl. Qed.
Lemma D_7be74 : decode_any W_7be74 = Some (Jal 1 2085800, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be78 : bv 32 := 0xcccff0ef.
Lemma F_7be78 : fetch_word AsanUbsan.M.loaded_segments (0x7be78 : word) = Some W_7be78.
Proof. vm_refl. Qed.
Lemma D_7be78 : decode_any W_7be78 = Some (Jal 1 2094284, 4%Z).
Proof. vm_refl. Qed.
