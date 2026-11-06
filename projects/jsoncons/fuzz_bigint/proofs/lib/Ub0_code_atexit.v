(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_202b8 : bv 32 := 0xff010113.
Lemma F_202b8 : fetch_word Ubsan.M.loaded_segments (0x202b8 : word) = Some W_202b8.
Proof. vm_refl. Qed.
Lemma D_202b8 : decode_any W_202b8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_202bc : bv 32 := 0x00113423.
Lemma F_202bc : fetch_word Ubsan.M.loaded_segments (0x202bc : word) = Some W_202bc.
Proof. vm_refl. Qed.
Lemma D_202bc : decode_any W_202bc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_202c0 : bv 32 := 0x00813023.
Lemma F_202c0 : fetch_word Ubsan.M.loaded_segments (0x202c0 : word) = Some W_202c0.
Proof. vm_refl. Qed.
Lemma D_202c0 : decode_any W_202c0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_202c4 : bv 32 := 0x01010413.
Lemma F_202c4 : fetch_word Ubsan.M.loaded_segments (0x202c4 : word) = Some W_202c4.
Proof. vm_refl. Qed.
Lemma D_202c4 : decode_any W_202c4 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_202c8 : bv 32 := 0x00040517.
Lemma F_202c8 : fetch_word Ubsan.M.loaded_segments (0x202c8 : word) = Some W_202c8.
Proof. vm_refl. Qed.
Lemma D_202c8 : decode_any W_202c8 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_202cc : bv 32 := 0x0f050513.
Lemma F_202cc : fetch_word Ubsan.M.loaded_segments (0x202cc : word) = Some W_202cc.
Proof. vm_refl. Qed.
Lemma D_202cc : decode_any W_202cc = Some (OpImm ALU_ADD 10 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_202d0 : bv 32 := 0x00054503.
Lemma F_202d0 : fetch_word Ubsan.M.loaded_segments (0x202d0 : word) = Some W_202d0.
Proof. vm_refl. Qed.
Lemma D_202d0 : decode_any W_202d0 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_202d4 : bv 32 := 0x00157513.
Lemma F_202d4 : fetch_word Ubsan.M.loaded_segments (0x202d4 : word) = Some W_202d4.
Proof. vm_refl. Qed.
Lemma D_202d4 : decode_any W_202d4 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_202d8 : bv 32 := 0x00050663.
Lemma F_202d8 : fetch_word Ubsan.M.loaded_segments (0x202d8 : word) = Some W_202d8.
Proof. vm_refl. Qed.
Lemma D_202d8 : decode_any W_202d8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_202e4 : bv 32 := 0x00040517.
Lemma F_202e4 : fetch_word Ubsan.M.loaded_segments (0x202e4 : word) = Some W_202e4.
Proof. vm_refl. Qed.
Lemma D_202e4 : decode_any W_202e4 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_202e8 : bv 32 := 0x0d450593.
Lemma F_202e8 : fetch_word Ubsan.M.loaded_segments (0x202e8 : word) = Some W_202e8.
Proof. vm_refl. Qed.
Lemma D_202e8 : decode_any W_202e8 = Some (OpImm ALU_ADD 11 10 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_202ec : bv 32 := 0x00100513.
Lemma F_202ec : fetch_word Ubsan.M.loaded_segments (0x202ec : word) = Some W_202ec.
Proof. vm_refl. Qed.
Lemma D_202ec : decode_any W_202ec = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_202f0 : bv 32 := 0x00a58023.
Lemma F_202f0 : fetch_word Ubsan.M.loaded_segments (0x202f0 : word) = Some W_202f0.
Proof. vm_refl. Qed.
Lemma D_202f0 : decode_any W_202f0 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_202f4 : bv 32 := 0x0003f517.
Lemma F_202f4 : fetch_word Ubsan.M.loaded_segments (0x202f4 : word) = Some W_202f4.
Proof. vm_refl. Qed.
Lemma D_202f4 : decode_any W_202f4 = Some (Auipc 10 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_202f8 : bv 32 := 0xccc53503.
Lemma F_202f8 : fetch_word Ubsan.M.loaded_segments (0x202f8 : word) = Some W_202f8.
Proof. vm_refl. Qed.
Lemma D_202f8 : decode_any W_202f8 = Some (Load SZ8 true 10 10 3276, 4%Z).
Proof. vm_refl. Qed.

Definition W_202fc : bv 32 := 0x00050e63.
Lemma F_202fc : fetch_word Ubsan.M.loaded_segments (0x202fc : word) = Some W_202fc.
Proof. vm_refl. Qed.
Lemma D_202fc : decode_any W_202fc = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_20300 : bv 32 := 0x0040006f.
Lemma F_20300 : fetch_word Ubsan.M.loaded_segments (0x20300 : word) = Some W_20300.
Proof. vm_refl. Qed.
Lemma D_20300 : decode_any W_20300 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_20304 : bv 32 := 0x00040517.
Lemma F_20304 : fetch_word Ubsan.M.loaded_segments (0x20304 : word) = Some W_20304.
Proof. vm_refl. Qed.
Lemma D_20304 : decode_any W_20304 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_20308 : bv 32 := 0xdfc50513.
Lemma F_20308 : fetch_word Ubsan.M.loaded_segments (0x20308 : word) = Some W_20308.
Proof. vm_refl. Qed.
Lemma D_20308 : decode_any W_20308 = Some (OpImm ALU_ADD 10 10 3580, 4%Z).
Proof. vm_refl. Qed.

Definition W_2030c : bv 32 := 0x00053503.
Lemma F_2030c : fetch_word Ubsan.M.loaded_segments (0x2030c : word) = Some W_2030c.
Proof. vm_refl. Qed.
Lemma D_2030c : decode_any W_2030c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20310 : bv 32 := 0x32d2b0ef.
Lemma F_20310 : fetch_word Ubsan.M.loaded_segments (0x20310 : word) = Some W_20310.
Proof. vm_refl. Qed.
Lemma D_20310 : decode_any W_20310 = Some (Jal 1 178988, 4%Z).
Proof. vm_refl. Qed.

Definition W_20314 : bv 32 := 0x0040006f.
Lemma F_20314 : fetch_word Ubsan.M.loaded_segments (0x20314 : word) = Some W_20314.
Proof. vm_refl. Qed.
Lemma D_20314 : decode_any W_20314 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_20318 : bv 32 := 0x0003f517.
Lemma F_20318 : fetch_word Ubsan.M.loaded_segments (0x20318 : word) = Some W_20318.
Proof. vm_refl. Qed.
Lemma D_20318 : decode_any W_20318 = Some (Auipc 10 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_2031c : bv 32 := 0xcb053503.
Lemma F_2031c : fetch_word Ubsan.M.loaded_segments (0x2031c : word) = Some W_2031c.
Proof. vm_refl. Qed.
Lemma D_2031c : decode_any W_2031c = Some (Load SZ8 true 10 10 3248, 4%Z).
Proof. vm_refl. Qed.

Definition W_20320 : bv 32 := 0x00050c63.
Lemma F_20320 : fetch_word Ubsan.M.loaded_segments (0x20320 : word) = Some W_20320.
Proof. vm_refl. Qed.
Lemma D_20320 : decode_any W_20320 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_20338 : bv 32 := 0x00813083.
Lemma F_20338 : fetch_word Ubsan.M.loaded_segments (0x20338 : word) = Some W_20338.
Proof. vm_refl. Qed.
Lemma D_20338 : decode_any W_20338 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2033c : bv 32 := 0x00013403.
Lemma F_2033c : fetch_word Ubsan.M.loaded_segments (0x2033c : word) = Some W_2033c.
Proof. vm_refl. Qed.
Lemma D_2033c : decode_any W_2033c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20340 : bv 32 := 0x01010113.
Lemma F_20340 : fetch_word Ubsan.M.loaded_segments (0x20340 : word) = Some W_20340.
Proof. vm_refl. Qed.
Lemma D_20340 : decode_any W_20340 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_20344 : bv 32 := 0x00008067.
Lemma F_20344 : fetch_word Ubsan.M.loaded_segments (0x20344 : word) = Some W_20344.
Proof. vm_refl. Qed.
Lemma D_20344 : decode_any W_20344 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20770 : bv 32 := 0x00050517.
Lemma F_20770 : fetch_word Ubsan.M.loaded_segments (0x20770 : word) = Some W_20770.
Proof. vm_refl. Qed.
Lemma D_20770 : decode_any W_20770 = Some (Auipc 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_20774 : bv 32 := 0xc5454503.
Lemma F_20774 : fetch_word Ubsan.M.loaded_segments (0x20774 : word) = Some W_20774.
Proof. vm_refl. Qed.
Lemma D_20774 : decode_any W_20774 = Some (Load SZ1 false 10 10 3156, 4%Z).
Proof. vm_refl. Qed.

Definition W_20778 : bv 32 := 0x00051463.
Lemma F_20778 : fetch_word Ubsan.M.loaded_segments (0x20778 : word) = Some W_20778.
Proof. vm_refl. Qed.
Lemma D_20778 : decode_any W_20778 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2077c : bv 32 := 0x00008067.
Lemma F_2077c : fetch_word Ubsan.M.loaded_segments (0x2077c : word) = Some W_2077c.
Proof. vm_refl. Qed.
Lemma D_2077c : decode_any W_2077c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd74 : bv 32 := 0xfd010113.
Lemma F_4bd74 : fetch_word Ubsan.M.loaded_segments (0x4bd74 : word) = Some W_4bd74.
Proof. vm_refl. Qed.
Lemma D_4bd74 : decode_any W_4bd74 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd78 : bv 32 := 0x02113423.
Lemma F_4bd78 : fetch_word Ubsan.M.loaded_segments (0x4bd78 : word) = Some W_4bd78.
Proof. vm_refl. Qed.
Lemma D_4bd78 : decode_any W_4bd78 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd7c : bv 32 := 0x02813023.
Lemma F_4bd7c : fetch_word Ubsan.M.loaded_segments (0x4bd7c : word) = Some W_4bd7c.
Proof. vm_refl. Qed.
Lemma D_4bd7c : decode_any W_4bd7c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd80 : bv 32 := 0x00913c23.
Lemma F_4bd80 : fetch_word Ubsan.M.loaded_segments (0x4bd80 : word) = Some W_4bd80.
Proof. vm_refl. Qed.
Lemma D_4bd80 : decode_any W_4bd80 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd84 : bv 32 := 0x01213823.
Lemma F_4bd84 : fetch_word Ubsan.M.loaded_segments (0x4bd84 : word) = Some W_4bd84.
Proof. vm_refl. Qed.
Lemma D_4bd84 : decode_any W_4bd84 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd88 : bv 32 := 0x01313423.
Lemma F_4bd88 : fetch_word Ubsan.M.loaded_segments (0x4bd88 : word) = Some W_4bd88.
Proof. vm_refl. Qed.
Lemma D_4bd88 : decode_any W_4bd88 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd8c : bv 32 := 0x00045517.
Lemma F_4bd8c : fetch_word Ubsan.M.loaded_segments (0x4bd8c : word) = Some W_4bd8c.
Proof. vm_refl. Qed.
Lemma D_4bd8c : decode_any W_4bd8c = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd90 : bv 32 := 0x1f450913.
Lemma F_4bd90 : fetch_word Ubsan.M.loaded_segments (0x4bd90 : word) = Some W_4bd90.
Proof. vm_refl. Qed.
Lemma D_4bd90 : decode_any W_4bd90 = Some (OpImm ALU_ADD 18 10 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd94 : bv 32 := 0x00490413.
Lemma F_4bd94 : fetch_word Ubsan.M.loaded_segments (0x4bd94 : word) = Some W_4bd94.
Proof. vm_refl. Qed.
Lemma D_4bd94 : decode_any W_4bd94 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd98 : bv 32 := 0x00040513.
Lemma F_4bd98 : fetch_word Ubsan.M.loaded_segments (0x4bd98 : word) = Some W_4bd98.
Proof. vm_refl. Qed.
Lemma D_4bd98 : decode_any W_4bd98 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd9c : bv 32 := 0x7890d0ef.
Lemma F_4bd9c : fetch_word Ubsan.M.loaded_segments (0x4bd9c : word) = Some W_4bd9c.
Proof. vm_refl. Qed.
Lemma D_4bd9c : decode_any W_4bd9c = Some (Jal 1 57224, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bda0 : bv 32 := 0x01093503.
Lemma F_4bda0 : fetch_word Ubsan.M.loaded_segments (0x4bda0 : word) = Some W_4bda0.
Proof. vm_refl. Qed.
Lemma D_4bda0 : decode_any W_4bda0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bda4 : bv 32 := 0x06050863.
Lemma F_4bda4 : fetch_word Ubsan.M.loaded_segments (0x4bda4 : word) = Some W_4bda4.
Proof. vm_refl. Qed.
Lemma D_4bda4 : decode_any W_4bda4 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bda8 : bv 32 := 0x00892583.
Lemma F_4bda8 : fetch_word Ubsan.M.loaded_segments (0x4bda8 : word) = Some W_4bda8.
Proof. vm_refl. Qed.
Lemma D_4bda8 : decode_any W_4bda8 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdac : bv 32 := 0x0180006f.
Lemma F_4bdac : fetch_word Ubsan.M.loaded_segments (0x4bdac : word) = Some W_4bdac.
Proof. vm_refl. Qed.
Lemma D_4bdac : decode_any W_4bdac = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdb0 : bv 32 := 0x00053503.
Lemma F_4bdb0 : fetch_word Ubsan.M.loaded_segments (0x4bdb0 : word) = Some W_4bdb0.
Proof. vm_refl. Qed.
Lemma D_4bdb0 : decode_any W_4bdb0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdb4 : bv 32 := 0x02000593.
Lemma F_4bdb4 : fetch_word Ubsan.M.loaded_segments (0x4bdb4 : word) = Some W_4bdb4.
Proof. vm_refl. Qed.
Lemma D_4bdb4 : decode_any W_4bdb4 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdb8 : bv 32 := 0x00b92423.
Lemma F_4bdb8 : fetch_word Ubsan.M.loaded_segments (0x4bdb8 : word) = Some W_4bdb8.
Proof. vm_refl. Qed.
Lemma D_4bdb8 : decode_any W_4bdb8 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdbc : bv 32 := 0x00a93823.
Lemma F_4bdbc : fetch_word Ubsan.M.loaded_segments (0x4bdbc : word) = Some W_4bdbc.
Proof. vm_refl. Qed.
Lemma D_4bdbc : decode_any W_4bdbc = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdc0 : bv 32 := 0x04050a63.
Lemma F_4bdc0 : fetch_word Ubsan.M.loaded_segments (0x4bdc0 : word) = Some W_4bdc0.
Proof. vm_refl. Qed.
Lemma D_4bdc0 : decode_any W_4bdc0 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdc4 : bv 32 := 0xfff5861b.
Lemma F_4bdc4 : fetch_word Ubsan.M.loaded_segments (0x4bdc4 : word) = Some W_4bdc4.
Proof. vm_refl. Qed.
Lemma D_4bdc4 : decode_any W_4bdc4 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdc8 : bv 32 := 0x00c92423.
Lemma F_4bdc8 : fetch_word Ubsan.M.loaded_segments (0x4bdc8 : word) = Some W_4bdc8.
Proof. vm_refl. Qed.
Lemma D_4bdc8 : decode_any W_4bdc8 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdcc : bv 32 := 0xfeb052e3.
Lemma F_4bdcc : fetch_word Ubsan.M.loaded_segments (0x4bdcc : word) = Some W_4bdcc.
Proof. vm_refl. Qed.
Lemma D_4bdcc : decode_any W_4bdcc = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdd0 : bv 32 := 0x01093503.
Lemma F_4bdd0 : fetch_word Ubsan.M.loaded_segments (0x4bdd0 : word) = Some W_4bdd0.
Proof. vm_refl. Qed.
Lemma D_4bdd0 : decode_any W_4bdd0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdd4 : bv 32 := 0x00361613.
Lemma F_4bdd4 : fetch_word Ubsan.M.loaded_segments (0x4bdd4 : word) = Some W_4bdd4.
Proof. vm_refl. Qed.
Lemma D_4bdd4 : decode_any W_4bdd4 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdd8 : bv 32 := 0x00c50533.
Lemma F_4bdd8 : fetch_word Ubsan.M.loaded_segments (0x4bdd8 : word) = Some W_4bdd8.
Proof. vm_refl. Qed.
Lemma D_4bdd8 : decode_any W_4bdd8 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bddc : bv 32 := 0x00853983.
Lemma F_4bddc : fetch_word Ubsan.M.loaded_segments (0x4bddc : word) = Some W_4bddc.
Proof. vm_refl. Qed.
Lemma D_4bddc : decode_any W_4bddc = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bde0 : bv 32 := 0x10853483.
Lemma F_4bde0 : fetch_word Ubsan.M.loaded_segments (0x4bde0 : word) = Some W_4bde0.
Proof. vm_refl. Qed.
Lemma D_4bde0 : decode_any W_4bde0 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bde4 : bv 32 := 0x00040513.
Lemma F_4bde4 : fetch_word Ubsan.M.loaded_segments (0x4bde4 : word) = Some W_4bde4.
Proof. vm_refl. Qed.
Lemma D_4bde4 : decode_any W_4bde4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bde8 : bv 32 := 0x1c40e0ef.
Lemma F_4bde8 : fetch_word Ubsan.M.loaded_segments (0x4bde8 : word) = Some W_4bde8.
Proof. vm_refl. Qed.
Lemma D_4bde8 : decode_any W_4bde8 = Some (Jal 1 57796, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdec : bv 32 := 0x00048513.
Lemma F_4bdec : fetch_word Ubsan.M.loaded_segments (0x4bdec : word) = Some W_4bdec.
Proof. vm_refl. Qed.
Lemma D_4bdec : decode_any W_4bdec = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdf0 : bv 32 := 0x000980e7.
Lemma F_4bdf0 : fetch_word Ubsan.M.loaded_segments (0x4bdf0 : word) = Some W_4bdf0.
Proof. vm_refl. Qed.
Lemma D_4bdf0 : decode_any W_4bdf0 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdf4 : bv 32 := 0x00040513.
Lemma F_4bdf4 : fetch_word Ubsan.M.loaded_segments (0x4bdf4 : word) = Some W_4bdf4.
Proof. vm_refl. Qed.
Lemma D_4bdf4 : decode_any W_4bdf4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdf8 : bv 32 := 0x72d0d0ef.
Lemma F_4bdf8 : fetch_word Ubsan.M.loaded_segments (0x4bdf8 : word) = Some W_4bdf8.
Proof. vm_refl. Qed.
Lemma D_4bdf8 : decode_any W_4bdf8 = Some (Jal 1 57132, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bdfc : bv 32 := 0x00892503.
Lemma F_4bdfc : fetch_word Ubsan.M.loaded_segments (0x4bdfc : word) = Some W_4bdfc.
Proof. vm_refl. Qed.
Lemma D_4bdfc : decode_any W_4bdfc = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be00 : bv 32 := 0xfff5061b.
Lemma F_4be00 : fetch_word Ubsan.M.loaded_segments (0x4be00 : word) = Some W_4be00.
Proof. vm_refl. Qed.
Lemma D_4be00 : decode_any W_4be00 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be04 : bv 32 := 0x00c92423.
Lemma F_4be04 : fetch_word Ubsan.M.loaded_segments (0x4be04 : word) = Some W_4be04.
Proof. vm_refl. Qed.
Lemma D_4be04 : decode_any W_4be04 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be08 : bv 32 := 0xfca044e3.
Lemma F_4be08 : fetch_word Ubsan.M.loaded_segments (0x4be08 : word) = Some W_4be08.
Proof. vm_refl. Qed.
Lemma D_4be08 : decode_any W_4be08 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be0c : bv 32 := 0x01093503.
Lemma F_4be0c : fetch_word Ubsan.M.loaded_segments (0x4be0c : word) = Some W_4be0c.
Proof. vm_refl. Qed.
Lemma D_4be0c : decode_any W_4be0c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be10 : bv 32 := 0xfa1ff06f.
Lemma F_4be10 : fetch_word Ubsan.M.loaded_segments (0x4be10 : word) = Some W_4be10.
Proof. vm_refl. Qed.
Lemma D_4be10 : decode_any W_4be10 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be14 : bv 32 := 0x00100513.
Lemma F_4be14 : fetch_word Ubsan.M.loaded_segments (0x4be14 : word) = Some W_4be14.
Proof. vm_refl. Qed.
Lemma D_4be14 : decode_any W_4be14 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be18 : bv 32 := 0x00a90023.
Lemma F_4be18 : fetch_word Ubsan.M.loaded_segments (0x4be18 : word) = Some W_4be18.
Proof. vm_refl. Qed.
Lemma D_4be18 : decode_any W_4be18 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be1c : bv 32 := 0x00040513.
Lemma F_4be1c : fetch_word Ubsan.M.loaded_segments (0x4be1c : word) = Some W_4be1c.
Proof. vm_refl. Qed.
Lemma D_4be1c : decode_any W_4be1c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be20 : bv 32 := 0x02813083.
Lemma F_4be20 : fetch_word Ubsan.M.loaded_segments (0x4be20 : word) = Some W_4be20.
Proof. vm_refl. Qed.
Lemma D_4be20 : decode_any W_4be20 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be24 : bv 32 := 0x02013403.
Lemma F_4be24 : fetch_word Ubsan.M.loaded_segments (0x4be24 : word) = Some W_4be24.
Proof. vm_refl. Qed.
Lemma D_4be24 : decode_any W_4be24 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be28 : bv 32 := 0x01813483.
Lemma F_4be28 : fetch_word Ubsan.M.loaded_segments (0x4be28 : word) = Some W_4be28.
Proof. vm_refl. Qed.
Lemma D_4be28 : decode_any W_4be28 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be2c : bv 32 := 0x01013903.
Lemma F_4be2c : fetch_word Ubsan.M.loaded_segments (0x4be2c : word) = Some W_4be2c.
Proof. vm_refl. Qed.
Lemma D_4be2c : decode_any W_4be2c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be30 : bv 32 := 0x00813983.
Lemma F_4be30 : fetch_word Ubsan.M.loaded_segments (0x4be30 : word) = Some W_4be30.
Proof. vm_refl. Qed.
Lemma D_4be30 : decode_any W_4be30 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be34 : bv 32 := 0x03010113.
Lemma F_4be34 : fetch_word Ubsan.M.loaded_segments (0x4be34 : word) = Some W_4be34.
Proof. vm_refl. Qed.
Lemma D_4be34 : decode_any W_4be34 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be38 : bv 32 := 0x1740e06f.
Lemma F_4be38 : fetch_word Ubsan.M.loaded_segments (0x4be38 : word) = Some W_4be38.
Proof. vm_refl. Qed.
Lemma D_4be38 : decode_any W_4be38 = Some (Jal 0 57716, 4%Z).
Proof. vm_refl. Qed.

Definition W_4be3c : bv 32 := 0x00008067.
Lemma F_4be3c : fetch_word Ubsan.M.loaded_segments (0x4be3c : word) = Some W_4be3c.
Proof. vm_refl. Qed.
Lemma D_4be3c : decode_any W_4be3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf04 : bv 32 := 0x00050067.
Lemma F_4bf04 : fetch_word Ubsan.M.loaded_segments (0x4bf04 : word) = Some W_4bf04.
Proof. vm_refl. Qed.
Lemma D_4bf04 : decode_any W_4bf04 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf08 : bv 32 := 0x00008067.
Lemma F_4bf08 : fetch_word Ubsan.M.loaded_segments (0x4bf08 : word) = Some W_4bf08.
Proof. vm_refl. Qed.
Lemma D_4bf08 : decode_any W_4bf08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf0c : bv 32 := 0xfe010113.
Lemma F_4bf0c : fetch_word Ubsan.M.loaded_segments (0x4bf0c : word) = Some W_4bf0c.
Proof. vm_refl. Qed.
Lemma D_4bf0c : decode_any W_4bf0c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf10 : bv 32 := 0x00113c23.
Lemma F_4bf10 : fetch_word Ubsan.M.loaded_segments (0x4bf10 : word) = Some W_4bf10.
Proof. vm_refl. Qed.
Lemma D_4bf10 : decode_any W_4bf10 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf14 : bv 32 := 0x00813823.
Lemma F_4bf14 : fetch_word Ubsan.M.loaded_segments (0x4bf14 : word) = Some W_4bf14.
Proof. vm_refl. Qed.
Lemma D_4bf14 : decode_any W_4bf14 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf18 : bv 32 := 0x00913423.
Lemma F_4bf18 : fetch_word Ubsan.M.loaded_segments (0x4bf18 : word) = Some W_4bf18.
Proof. vm_refl. Qed.
Lemma D_4bf18 : decode_any W_4bf18 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf1c : bv 32 := 0x00013517.
Lemma F_4bf1c : fetch_word Ubsan.M.loaded_segments (0x4bf1c : word) = Some W_4bf1c.
Proof. vm_refl. Qed.
Lemma D_4bf1c : decode_any W_4bf1c = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf20 : bv 32 := 0x00013597.
Lemma F_4bf20 : fetch_word Ubsan.M.loaded_segments (0x4bf20 : word) = Some W_4bf20.
Proof. vm_refl. Qed.
Lemma D_4bf20 : decode_any W_4bf20 = Some (Auipc 11 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf24 : bv 32 := 0x1d453503.
Lemma F_4bf24 : fetch_word Ubsan.M.loaded_segments (0x4bf24 : word) = Some W_4bf24.
Proof. vm_refl. Qed.
Lemma D_4bf24 : decode_any W_4bf24 = Some (Load SZ8 true 10 10 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf28 : bv 32 := 0x1d85b403.
Lemma F_4bf28 : fetch_word Ubsan.M.loaded_segments (0x4bf28 : word) = Some W_4bf28.
Proof. vm_refl. Qed.
Lemma D_4bf28 : decode_any W_4bf28 = Some (Load SZ8 true 8 11 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf2c : bv 32 := 0x00a47c63.
Lemma F_4bf2c : fetch_word Ubsan.M.loaded_segments (0x4bf2c : word) = Some W_4bf2c.
Proof. vm_refl. Qed.
Lemma D_4bf2c : decode_any W_4bf2c = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf30 : bv 32 := 0xff853583.
Lemma F_4bf30 : fetch_word Ubsan.M.loaded_segments (0x4bf30 : word) = Some W_4bf30.
Proof. vm_refl. Qed.
Lemma D_4bf30 : decode_any W_4bf30 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf34 : bv 32 := 0xff850493.
Lemma F_4bf34 : fetch_word Ubsan.M.loaded_segments (0x4bf34 : word) = Some W_4bf34.
Proof. vm_refl. Qed.
Lemma D_4bf34 : decode_any W_4bf34 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf38 : bv 32 := 0x000580e7.
Lemma F_4bf38 : fetch_word Ubsan.M.loaded_segments (0x4bf38 : word) = Some W_4bf38.
Proof. vm_refl. Qed.
Lemma D_4bf38 : decode_any W_4bf38 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf3c : bv 32 := 0x00048513.
Lemma F_4bf3c : fetch_word Ubsan.M.loaded_segments (0x4bf3c : word) = Some W_4bf3c.
Proof. vm_refl. Qed.
Lemma D_4bf3c : decode_any W_4bf3c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf40 : bv 32 := 0xfe9468e3.
Lemma F_4bf40 : fetch_word Ubsan.M.loaded_segments (0x4bf40 : word) = Some W_4bf40.
Proof. vm_refl. Qed.
Lemma D_4bf40 : decode_any W_4bf40 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf44 : bv 32 := 0x01813083.
Lemma F_4bf44 : fetch_word Ubsan.M.loaded_segments (0x4bf44 : word) = Some W_4bf44.
Proof. vm_refl. Qed.
Lemma D_4bf44 : decode_any W_4bf44 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf48 : bv 32 := 0x01013403.
Lemma F_4bf48 : fetch_word Ubsan.M.loaded_segments (0x4bf48 : word) = Some W_4bf48.
Proof. vm_refl. Qed.
Lemma D_4bf48 : decode_any W_4bf48 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf4c : bv 32 := 0x00813483.
Lemma F_4bf4c : fetch_word Ubsan.M.loaded_segments (0x4bf4c : word) = Some W_4bf4c.
Proof. vm_refl. Qed.
Lemma D_4bf4c : decode_any W_4bf4c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf50 : bv 32 := 0x02010113.
Lemma F_4bf50 : fetch_word Ubsan.M.loaded_segments (0x4bf50 : word) = Some W_4bf50.
Proof. vm_refl. Qed.
Lemma D_4bf50 : decode_any W_4bf50 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf54 : bv 32 := 0xfb5ff06f.
Lemma F_4bf54 : fetch_word Ubsan.M.loaded_segments (0x4bf54 : word) = Some W_4bf54.
Proof. vm_refl. Qed.
Lemma D_4bf54 : decode_any W_4bf54 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf58 : bv 32 := 0xff010113.
Lemma F_4bf58 : fetch_word Ubsan.M.loaded_segments (0x4bf58 : word) = Some W_4bf58.
Proof. vm_refl. Qed.
Lemma D_4bf58 : decode_any W_4bf58 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf5c : bv 32 := 0x00113423.
Lemma F_4bf5c : fetch_word Ubsan.M.loaded_segments (0x4bf5c : word) = Some W_4bf5c.
Proof. vm_refl. Qed.
Lemma D_4bf5c : decode_any W_4bf5c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf60 : bv 32 := 0x00813023.
Lemma F_4bf60 : fetch_word Ubsan.M.loaded_segments (0x4bf60 : word) = Some W_4bf60.
Proof. vm_refl. Qed.
Lemma D_4bf60 : decode_any W_4bf60 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf64 : bv 32 := 0x00000593.
Lemma F_4bf64 : fetch_word Ubsan.M.loaded_segments (0x4bf64 : word) = Some W_4bf64.
Proof. vm_refl. Qed.
Lemma D_4bf64 : decode_any W_4bf64 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf68 : bv 32 := 0x00020613.
Lemma F_4bf68 : fetch_word Ubsan.M.loaded_segments (0x4bf68 : word) = Some W_4bf68.
Proof. vm_refl. Qed.
Lemma D_4bf68 : decode_any W_4bf68 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf6c : bv 32 := 0xf5862603.
Lemma F_4bf6c : fetch_word Ubsan.M.loaded_segments (0x4bf6c : word) = Some W_4bf6c.
Proof. vm_refl. Qed.
Lemma D_4bf6c : decode_any W_4bf6c = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf70 : bv 32 := 0x00045697.
Lemma F_4bf70 : fetch_word Ubsan.M.loaded_segments (0x4bf70 : word) = Some W_4bf70.
Proof. vm_refl. Qed.
Lemma D_4bf70 : decode_any W_4bf70 = Some (Auipc 13 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf74 : bv 32 := 0x23068693.
Lemma F_4bf74 : fetch_word Ubsan.M.loaded_segments (0x4bf74 : word) = Some W_4bf74.
Proof. vm_refl. Qed.
Lemma D_4bf74 : decode_any W_4bf74 = Some (OpImm ALU_ADD 13 13 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf78 : bv 32 := 0x1606a72f.
Lemma F_4bf78 : fetch_word Ubsan.M.loaded_segments (0x4bf78 : word) = Some W_4bf78.
Proof. vm_refl. Qed.
Lemma D_4bf78 : decode_any W_4bf78 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf7c : bv 32 := 0x00b71663.
Lemma F_4bf7c : fetch_word Ubsan.M.loaded_segments (0x4bf7c : word) = Some W_4bf7c.
Proof. vm_refl. Qed.
Lemma D_4bf7c : decode_any W_4bf7c = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf80 : bv 32 := 0x1ec6a7af.
Lemma F_4bf80 : fetch_word Ubsan.M.loaded_segments (0x4bf80 : word) = Some W_4bf80.
Proof. vm_refl. Qed.
Lemma D_4bf80 : decode_any W_4bf80 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf84 : bv 32 := 0xfe079ae3.
Lemma F_4bf84 : fetch_word Ubsan.M.loaded_segments (0x4bf84 : word) = Some W_4bf84.
Proof. vm_refl. Qed.
Lemma D_4bf84 : decode_any W_4bf84 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf88 : bv 32 := 0x0007059b.
Lemma F_4bf88 : fetch_word Ubsan.M.loaded_segments (0x4bf88 : word) = Some W_4bf88.
Proof. vm_refl. Qed.
Lemma D_4bf88 : decode_any W_4bf88 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf8c : bv 32 := 0x02c58263.
Lemma F_4bf8c : fetch_word Ubsan.M.loaded_segments (0x4bf8c : word) = Some W_4bf8c.
Proof. vm_refl. Qed.
Lemma D_4bf8c : decode_any W_4bf8c = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf90 : bv 32 := 0x02058263.
Lemma F_4bf90 : fetch_word Ubsan.M.loaded_segments (0x4bf90 : word) = Some W_4bf90.
Proof. vm_refl. Qed.
Lemma D_4bf90 : decode_any W_4bf90 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bfb4 : bv 32 := 0x00050413.
Lemma F_4bfb4 : fetch_word Ubsan.M.loaded_segments (0x4bfb4 : word) = Some W_4bfb4.
Proof. vm_refl. Qed.
Lemma D_4bfb4 : decode_any W_4bfb4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bfb8 : bv 32 := 0xdbdff0ef.
Lemma F_4bfb8 : fetch_word Ubsan.M.loaded_segments (0x4bfb8 : word) = Some W_4bfb8.
Proof. vm_refl. Qed.
Lemma D_4bfb8 : decode_any W_4bfb8 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bfbc : bv 32 := 0xf51ff0ef.
Lemma F_4bfbc : fetch_word Ubsan.M.loaded_segments (0x4bfbc : word) = Some W_4bfbc.
Proof. vm_refl. Qed.
Lemma D_4bfbc : decode_any W_4bfbc = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bfc0 : bv 32 := 0x561020ef.
Lemma F_4bfc0 : fetch_word Ubsan.M.loaded_segments (0x4bfc0 : word) = Some W_4bfc0.
Proof. vm_refl. Qed.
Lemma D_4bfc0 : decode_any W_4bfc0 = Some (Jal 1 11616, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d24 : bv 32 := 0x00037597.
Lemma F_59d24 : fetch_word Ubsan.M.loaded_segments (0x59d24 : word) = Some W_59d24.
Proof. vm_refl. Qed.
Lemma D_59d24 : decode_any W_59d24 = Some (Auipc 11 55, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d28 : bv 32 := 0x4a758683.
Lemma F_59d28 : fetch_word Ubsan.M.loaded_segments (0x59d28 : word) = Some W_59d28.
Proof. vm_refl. Qed.
Lemma D_59d28 : decode_any W_59d28 = Some (Load SZ1 true 13 11 1191, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d2c : bv 32 := 0x1e068863.
Lemma F_59d2c : fetch_word Ubsan.M.loaded_segments (0x59d2c : word) = Some W_59d2c.
Proof. vm_refl. Qed.
Lemma D_59d2c : decode_any W_59d2c = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_59f1c : bv 32 := 0x00008067.
Lemma F_59f1c : fetch_word Ubsan.M.loaded_segments (0x59f1c : word) = Some W_59f1c.
Proof. vm_refl. Qed.
Lemma D_59f1c : decode_any W_59f1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59fac : bv 32 := 0x00052583.
Lemma F_59fac : fetch_word Ubsan.M.loaded_segments (0x59fac : word) = Some W_59fac.
Proof. vm_refl. Qed.
Lemma D_59fac : decode_any W_59fac = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59fb0 : bv 32 := 0x0005c463.
Lemma F_59fb0 : fetch_word Ubsan.M.loaded_segments (0x59fb0 : word) = Some W_59fb0.
Proof. vm_refl. Qed.
Lemma D_59fb0 : decode_any W_59fb0 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59fb4 : bv 32 := 0x00008067.
Lemma F_59fb4 : fetch_word Ubsan.M.loaded_segments (0x59fb4 : word) = Some W_59fb4.
Proof. vm_refl. Qed.
Lemma D_59fb4 : decode_any W_59fb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
