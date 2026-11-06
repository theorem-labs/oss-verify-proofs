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

Definition W_a2504 : bv 32 := 0xfc010113.
Lemma F_a2504 : fetch_word AsanUbsan.M.loaded_segments (0xa254c : word) = Some W_a2504.
Proof. vm_refl. Qed.
Lemma D_a2504 : decode_any W_a2504 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2508 : bv 32 := 0x02113c23.
Lemma F_a2508 : fetch_word AsanUbsan.M.loaded_segments (0xa2550 : word) = Some W_a2508.
Proof. vm_refl. Qed.
Lemma D_a2508 : decode_any W_a2508 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a250c : bv 32 := 0x02813823.
Lemma F_a250c : fetch_word AsanUbsan.M.loaded_segments (0xa2554 : word) = Some W_a250c.
Proof. vm_refl. Qed.
Lemma D_a250c : decode_any W_a250c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2510 : bv 32 := 0x02913423.
Lemma F_a2510 : fetch_word AsanUbsan.M.loaded_segments (0xa2558 : word) = Some W_a2510.
Proof. vm_refl. Qed.
Lemma D_a2510 : decode_any W_a2510 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2514 : bv 32 := 0x03213023.
Lemma F_a2514 : fetch_word AsanUbsan.M.loaded_segments (0xa255c : word) = Some W_a2514.
Proof. vm_refl. Qed.
Lemma D_a2514 : decode_any W_a2514 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2518 : bv 32 := 0x01313c23.
Lemma F_a2518 : fetch_word AsanUbsan.M.loaded_segments (0xa2560 : word) = Some W_a2518.
Proof. vm_refl. Qed.
Lemma D_a2518 : decode_any W_a2518 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a251c : bv 32 := 0x01413823.
Lemma F_a251c : fetch_word AsanUbsan.M.loaded_segments (0xa2564 : word) = Some W_a251c.
Proof. vm_refl. Qed.
Lemma D_a251c : decode_any W_a251c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2520 : bv 32 := 0x01513423.
Lemma F_a2520 : fetch_word AsanUbsan.M.loaded_segments (0xa2568 : word) = Some W_a2520.
Proof. vm_refl. Qed.
Lemma D_a2520 : decode_any W_a2520 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2524 : bv 32 := 0x00058413.
Lemma F_a2524 : fetch_word AsanUbsan.M.loaded_segments (0xa256c : word) = Some W_a2524.
Proof. vm_refl. Qed.
Lemma D_a2524 : decode_any W_a2524 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2528 : bv 32 := 0x0015b593.
Lemma F_a2528 : fetch_word AsanUbsan.M.loaded_segments (0xa2570 : word) = Some W_a2528.
Proof. vm_refl. Qed.
Lemma D_a2528 : decode_any W_a2528 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a252c : bv 32 := 0x7ff50293.
Lemma F_a252c : fetch_word AsanUbsan.M.loaded_segments (0xa2574 : word) = Some W_a252c.
Proof. vm_refl. Qed.
Lemma D_a252c : decode_any W_a252c = Some (OpImm ALU_ADD 5 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2530 : bv 32 := 0xfff58593.
Lemma F_a2530 : fetch_word AsanUbsan.M.loaded_segments (0xa2578 : word) = Some W_a2530.
Proof. vm_refl. Qed.
Lemma D_a2530 : decode_any W_a2530 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2534 : bv 32 := 0x00d5f333.
Lemma F_a2534 : fetch_word AsanUbsan.M.loaded_segments (0xa257c : word) = Some W_a2534.
Proof. vm_refl. Qed.
Lemma D_a2534 : decode_any W_a2534 = Some (Op ALU_AND 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2538 : bv 32 := 0x00100593.
Lemma F_a2538 : fetch_word AsanUbsan.M.loaded_segments (0xa2580 : word) = Some W_a2538.
Proof. vm_refl. Qed.
Lemma D_a2538 : decode_any W_a2538 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a253c : bv 32 := 0x0062b4a3.
Lemma F_a253c : fetch_word AsanUbsan.M.loaded_segments (0xa2584 : word) = Some W_a253c.
Proof. vm_refl. Qed.
Lemma D_a253c : decode_any W_a253c = Some (Store SZ8 5 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2540 : bv 32 := 0x00b40863.
Lemma F_a2540 : fetch_word AsanUbsan.M.loaded_segments (0xa2588 : word) = Some W_a2540.
Proof. vm_refl. Qed.
Lemma D_a2540 : decode_any W_a2540 = Some (Branch BC_EQ 8 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2544 : bv 32 := 0x02041c63.
Lemma F_a2544 : fetch_word AsanUbsan.M.loaded_segments (0xa258c : word) = Some W_a2544.
Proof. vm_refl. Qed.
Lemma D_a2544 : decode_any W_a2544 = Some (Branch BC_NE 8 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a257c : bv 32 := 0x06089463.
Lemma F_a257c : fetch_word AsanUbsan.M.loaded_segments (0xa25c4 : word) = Some W_a257c.
Proof. vm_refl. Qed.
Lemma D_a257c : decode_any W_a257c = Some (Branch BC_NE 17 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a25e4 : bv 32 := 0x00060593.
Lemma F_a25e4 : fetch_word AsanUbsan.M.loaded_segments (0xa262c : word) = Some W_a25e4.
Proof. vm_refl. Qed.
Lemma D_a25e4 : decode_any W_a25e4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a25e8 : bv 32 := 0x00068613.
Lemma F_a25e8 : fetch_word AsanUbsan.M.loaded_segments (0xa2630 : word) = Some W_a25e8.
Proof. vm_refl. Qed.
Lemma D_a25e8 : decode_any W_a25e8 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a25ec : bv 32 := 0x00078693.
Lemma F_a25ec : fetch_word AsanUbsan.M.loaded_segments (0xa2634 : word) = Some W_a25ec.
Proof. vm_refl. Qed.
Lemma D_a25ec : decode_any W_a25ec = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a25f0 : bv 32 := 0x00080713.
Lemma F_a25f0 : fetch_word AsanUbsan.M.loaded_segments (0xa2638 : word) = Some W_a25f0.
Proof. vm_refl. Qed.
Lemma D_a25f0 : decode_any W_a25f0 = Some (OpImm ALU_ADD 14 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a25f4 : bv 32 := 0x00040793.
Lemma F_a25f4 : fetch_word AsanUbsan.M.loaded_segments (0xa263c : word) = Some W_a25f4.
Proof. vm_refl. Qed.
Lemma D_a25f4 : decode_any W_a25f4 = Some (OpImm ALU_ADD 15 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a25f8 : bv 32 := 0x03813083.
Lemma F_a25f8 : fetch_word AsanUbsan.M.loaded_segments (0xa2640 : word) = Some W_a25f8.
Proof. vm_refl. Qed.
Lemma D_a25f8 : decode_any W_a25f8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a25fc : bv 32 := 0x03013403.
Lemma F_a25fc : fetch_word AsanUbsan.M.loaded_segments (0xa2644 : word) = Some W_a25fc.
Proof. vm_refl. Qed.
Lemma D_a25fc : decode_any W_a25fc = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2600 : bv 32 := 0x02813483.
Lemma F_a2600 : fetch_word AsanUbsan.M.loaded_segments (0xa2648 : word) = Some W_a2600.
Proof. vm_refl. Qed.
Lemma D_a2600 : decode_any W_a2600 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2604 : bv 32 := 0x02013903.
Lemma F_a2604 : fetch_word AsanUbsan.M.loaded_segments (0xa264c : word) = Some W_a2604.
Proof. vm_refl. Qed.
Lemma D_a2604 : decode_any W_a2604 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2608 : bv 32 := 0x01813983.
Lemma F_a2608 : fetch_word AsanUbsan.M.loaded_segments (0xa2650 : word) = Some W_a2608.
Proof. vm_refl. Qed.
Lemma D_a2608 : decode_any W_a2608 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a260c : bv 32 := 0x01013a03.
Lemma F_a260c : fetch_word AsanUbsan.M.loaded_segments (0xa2654 : word) = Some W_a260c.
Proof. vm_refl. Qed.
Lemma D_a260c : decode_any W_a260c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2610 : bv 32 := 0x00813a83.
Lemma F_a2610 : fetch_word AsanUbsan.M.loaded_segments (0xa2658 : word) = Some W_a2610.
Proof. vm_refl. Qed.
Lemma D_a2610 : decode_any W_a2610 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2614 : bv 32 := 0x04010113.
Lemma F_a2614 : fetch_word AsanUbsan.M.loaded_segments (0xa265c : word) = Some W_a2614.
Proof. vm_refl. Qed.
Lemma D_a2614 : decode_any W_a2614 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2618 : bv 32 := 0x891ff06f.
Lemma F_a2618 : fetch_word AsanUbsan.M.loaded_segments (0xa2660 : word) = Some W_a2618.
Proof. vm_refl. Qed.
Lemma D_a2618 : decode_any W_a2618 = Some (Jal 0 2095248, 4%Z).
Proof. vm_refl. Qed.

