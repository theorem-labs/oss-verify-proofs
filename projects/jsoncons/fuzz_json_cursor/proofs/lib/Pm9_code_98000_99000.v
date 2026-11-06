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

Definition W_9856c : bv 32 := 0xf7010113.
Lemma F_9856c : fetch_word AsanUbsan.M.loaded_segments (0x985b4 : word) = Some W_9856c.
Proof. vm_refl. Qed.
Lemma D_9856c : decode_any W_9856c = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_98570 : bv 32 := 0x08113423.
Lemma F_98570 : fetch_word AsanUbsan.M.loaded_segments (0x985b8 : word) = Some W_98570.
Proof. vm_refl. Qed.
Lemma D_98570 : decode_any W_98570 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_98574 : bv 32 := 0x08813023.
Lemma F_98574 : fetch_word AsanUbsan.M.loaded_segments (0x985bc : word) = Some W_98574.
Proof. vm_refl. Qed.
Lemma D_98574 : decode_any W_98574 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_98578 : bv 32 := 0x06913c23.
Lemma F_98578 : fetch_word AsanUbsan.M.loaded_segments (0x985c0 : word) = Some W_98578.
Proof. vm_refl. Qed.
Lemma D_98578 : decode_any W_98578 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_9857c : bv 32 := 0x07213823.
Lemma F_9857c : fetch_word AsanUbsan.M.loaded_segments (0x985c4 : word) = Some W_9857c.
Proof. vm_refl. Qed.
Lemma D_9857c : decode_any W_9857c = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_98580 : bv 32 := 0x07313423.
Lemma F_98580 : fetch_word AsanUbsan.M.loaded_segments (0x985c8 : word) = Some W_98580.
Proof. vm_refl. Qed.
Lemma D_98580 : decode_any W_98580 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_98584 : bv 32 := 0x07413023.
Lemma F_98584 : fetch_word AsanUbsan.M.loaded_segments (0x985cc : word) = Some W_98584.
Proof. vm_refl. Qed.
Lemma D_98584 : decode_any W_98584 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_98588 : bv 32 := 0x05513c23.
Lemma F_98588 : fetch_word AsanUbsan.M.loaded_segments (0x985d0 : word) = Some W_98588.
Proof. vm_refl. Qed.
Lemma D_98588 : decode_any W_98588 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_9858c : bv 32 := 0x05613823.
Lemma F_9858c : fetch_word AsanUbsan.M.loaded_segments (0x985d4 : word) = Some W_9858c.
Proof. vm_refl. Qed.
Lemma D_9858c : decode_any W_9858c = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_98590 : bv 32 := 0x05713423.
Lemma F_98590 : fetch_word AsanUbsan.M.loaded_segments (0x985d8 : word) = Some W_98590.
Proof. vm_refl. Qed.
Lemma D_98590 : decode_any W_98590 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_98594 : bv 32 := 0x05813023.
Lemma F_98594 : fetch_word AsanUbsan.M.loaded_segments (0x985dc : word) = Some W_98594.
Proof. vm_refl. Qed.
Lemma D_98594 : decode_any W_98594 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_98598 : bv 32 := 0x03913c23.
Lemma F_98598 : fetch_word AsanUbsan.M.loaded_segments (0x985e0 : word) = Some W_98598.
Proof. vm_refl. Qed.
Lemma D_98598 : decode_any W_98598 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9859c : bv 32 := 0x03a13823.
Lemma F_9859c : fetch_word AsanUbsan.M.loaded_segments (0x985e4 : word) = Some W_9859c.
Proof. vm_refl. Qed.
Lemma D_9859c : decode_any W_9859c = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_985a0 : bv 32 := 0x03b13423.
Lemma F_985a0 : fetch_word AsanUbsan.M.loaded_segments (0x985e8 : word) = Some W_985a0.
Proof. vm_refl. Qed.
Lemma D_985a0 : decode_any W_985a0 = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_985a4 : bv 32 := 0x00058913.
Lemma F_985a4 : fetch_word AsanUbsan.M.loaded_segments (0x985ec : word) = Some W_985a4.
Proof. vm_refl. Qed.
Lemma D_985a4 : decode_any W_985a4 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_985a8 : bv 32 := 0x000bc597.
Lemma F_985a8 : fetch_word AsanUbsan.M.loaded_segments (0x985f0 : word) = Some W_985a8.
Proof. vm_refl. Qed.
Lemma D_985a8 : decode_any W_985a8 = Some (Auipc 11 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_985ac : bv 32 := 0xf005b583.
Lemma F_985ac : fetch_word AsanUbsan.M.loaded_segments (0x985f4 : word) = Some W_985ac.
Proof. vm_refl. Qed.
Lemma D_985ac : decode_any W_985ac = Some (Load SZ8 true 11 11 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_985b0 : bv 32 := 0x0895c583.
Lemma F_985b0 : fetch_word AsanUbsan.M.loaded_segments (0x985f8 : word) = Some W_985b0.
Proof. vm_refl. Qed.
Lemma D_985b0 : decode_any W_985b0 = Some (Load SZ1 false 11 11 137, 4%Z).
Proof. vm_refl. Qed.

Definition W_985b4 : bv 32 := 0x18058a63.
Lemma F_985b4 : fetch_word AsanUbsan.M.loaded_segments (0x985fc : word) = Some W_985b4.
Proof. vm_refl. Qed.
Lemma D_985b4 : decode_any W_985b4 = Some (Branch BC_EQ 11 0 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_985b8 : bv 32 := 0x00050993.
Lemma F_985b8 : fetch_word AsanUbsan.M.loaded_segments (0x98600 : word) = Some W_985b8.
Proof. vm_refl. Qed.
Lemma D_985b8 : decode_any W_985b8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_985bc : bv 32 := 0x000bc517.
Lemma F_985bc : fetch_word AsanUbsan.M.loaded_segments (0x98604 : word) = Some W_985bc.
Proof. vm_refl. Qed.
Lemma D_985bc : decode_any W_985bc = Some (Auipc 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_985c0 : bv 32 := 0xf4c53d03.
Lemma F_985c0 : fetch_word AsanUbsan.M.loaded_segments (0x98608 : word) = Some W_985c0.
Proof. vm_refl. Qed.
Lemma D_985c0 : decode_any W_985c0 = Some (Load SZ8 true 26 10 3916, 4%Z).
Proof. vm_refl. Qed.

Definition W_985c4 : bv 32 := 0x0009ba03.
Lemma F_985c4 : fetch_word AsanUbsan.M.loaded_segments (0x9860c : word) = Some W_985c4.
Proof. vm_refl. Qed.
Lemma D_985c4 : decode_any W_985c4 = Some (Load SZ8 true 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_985c8 : bv 32 := 0x000bd517.
Lemma F_985c8 : fetch_word AsanUbsan.M.loaded_segments (0x98610 : word) = Some W_985c8.
Proof. vm_refl. Qed.
Lemma D_985c8 : decode_any W_985c8 = Some (Auipc 10 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_985cc : bv 32 := 0x000d2583.
Lemma F_985cc : fetch_word AsanUbsan.M.loaded_segments (0x98614 : word) = Some W_985cc.
Proof. vm_refl. Qed.
Lemma D_985cc : decode_any W_985cc = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_985d0 : bv 32 := 0xd1053a83.
Lemma F_985d0 : fetch_word AsanUbsan.M.loaded_segments (0x98618 : word) = Some W_985d0.
Proof. vm_refl. Qed.
Lemma D_985d0 : decode_any W_985d0 = Some (Load SZ8 true 21 10 3344, 4%Z).
Proof. vm_refl. Qed.

Definition W_985d4 : bv 32 := 0x00300513.
Lemma F_985d4 : fetch_word AsanUbsan.M.loaded_segments (0x9861c : word) = Some W_985d4.
Proof. vm_refl. Qed.
Lemma D_985d4 : decode_any W_985d4 = Some (OpImm ALU_ADD 10 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_985d8 : bv 32 := 0x004a8ab3.
Lemma F_985d8 : fetch_word AsanUbsan.M.loaded_segments (0x98620 : word) = Some W_985d8.
Proof. vm_refl. Qed.
Lemma D_985d8 : decode_any W_985d8 = Some (Op ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_985dc : bv 32 := 0x1ea5fa63.
Lemma F_985dc : fetch_word AsanUbsan.M.loaded_segments (0x98624 : word) = Some W_985dc.
Proof. vm_refl. Qed.
Lemma D_985dc : decode_any W_985dc = Some (Branch BC_GEU 11 10 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_985e0 : bv 32 := 0x000abb03.
Lemma F_985e0 : fetch_word AsanUbsan.M.loaded_segments (0x98628 : word) = Some W_985e0.
Proof. vm_refl. Qed.
Lemma D_985e0 : decode_any W_985e0 = Some (Load SZ8 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_985e4 : bv 32 := 0xfff00513.
Lemma F_985e4 : fetch_word AsanUbsan.M.loaded_segments (0x9862c : word) = Some W_985e4.
Proof. vm_refl. Qed.
Lemma D_985e4 : decode_any W_985e4 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_985e8 : bv 32 := 0x0230000f.
Lemma F_985e8 : fetch_word AsanUbsan.M.loaded_segments (0x98630 : word) = Some W_985e8.
Proof. vm_refl. Qed.
Lemma D_985e8 : decode_any W_985e8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_985ec : bv 32 := 0x14ab0e63.
Lemma F_985ec : fetch_word AsanUbsan.M.loaded_segments (0x98634 : word) = Some W_985ec.
Proof. vm_refl. Qed.
Lemma D_985ec : decode_any W_985ec = Some (Branch BC_EQ 22 10 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_985f0 : bv 32 := 0x080b1263.
Lemma F_985f0 : fetch_word AsanUbsan.M.loaded_segments (0x98638 : word) = Some W_985f0.
Proof. vm_refl. Qed.
Lemma D_985f0 : decode_any W_985f0 = Some (Branch BC_NE 22 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_98674 : bv 32 := 0x0c0b0a63.
Lemma F_98674 : fetch_word AsanUbsan.M.loaded_segments (0x986bc : word) = Some W_98674.
Proof. vm_refl. Qed.
Lemma D_98674 : decode_any W_98674 = Some (Branch BC_EQ 22 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_98678 : bv 32 := 0x00c13823.
Lemma F_98678 : fetch_word AsanUbsan.M.loaded_segments (0x986c0 : word) = Some W_98678.
Proof. vm_refl. Qed.
Lemma D_98678 : decode_any W_98678 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9867c : bv 32 := 0x00d13c23.
Lemma F_9867c : fetch_word AsanUbsan.M.loaded_segments (0x986c4 : word) = Some W_9867c.
Proof. vm_refl. Qed.
Lemma D_9867c : decode_any W_9867c = Some (Store SZ8 2 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_98680 : bv 32 := 0x0ff00513.
Lemma F_98680 : fetch_word AsanUbsan.M.loaded_segments (0x986c8 : word) = Some W_98680.
Proof. vm_refl. Qed.
Lemma D_98680 : decode_any W_98680 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_98684 : bv 32 := 0x0aaa6863.
Lemma F_98684 : fetch_word AsanUbsan.M.loaded_segments (0x986cc : word) = Some W_98684.
Proof. vm_refl. Qed.
Lemma D_98684 : decode_any W_98684 = Some (Branch BC_LTU 20 10 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_98734 : bv 32 := 0x000b0513.
Lemma F_98734 : fetch_word AsanUbsan.M.loaded_segments (0x9877c : word) = Some W_98734.
Proof. vm_refl. Qed.
Lemma D_98734 : decode_any W_98734 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98738 : bv 32 := 0x004a1413.
Lemma F_98738 : fetch_word AsanUbsan.M.loaded_segments (0x98780 : word) = Some W_98738.
Proof. vm_refl. Qed.
Lemma D_98738 : decode_any W_98738 = Some (ShiftImm ALU_SLL 8 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9873c : bv 32 := 0x00850433.
Lemma F_9873c : fetch_word AsanUbsan.M.loaded_segments (0x98784 : word) = Some W_9873c.
Proof. vm_refl. Qed.
Lemma D_9873c : decode_any W_9873c = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98740 : bv 32 := 0x00843503.
Lemma F_98740 : fetch_word AsanUbsan.M.loaded_segments (0x98788 : word) = Some W_98740.
Proof. vm_refl. Qed.
Lemma D_98740 : decode_any W_98740 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98744 : bv 32 := 0x04050263.
Lemma F_98744 : fetch_word AsanUbsan.M.loaded_segments (0x9878c : word) = Some W_98744.
Proof. vm_refl. Qed.
Lemma D_98744 : decode_any W_98744 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_98748 : bv 32 := 0x00000513.
Lemma F_98748 : fetch_word AsanUbsan.M.loaded_segments (0x98790 : word) = Some W_98748.
Proof. vm_refl. Qed.
Lemma D_98748 : decode_any W_98748 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9874c : bv 32 := 0x08813083.
Lemma F_9874c : fetch_word AsanUbsan.M.loaded_segments (0x98794 : word) = Some W_9874c.
Proof. vm_refl. Qed.
Lemma D_9874c : decode_any W_9874c = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_98750 : bv 32 := 0x08013403.
Lemma F_98750 : fetch_word AsanUbsan.M.loaded_segments (0x98798 : word) = Some W_98750.
Proof. vm_refl. Qed.
Lemma D_98750 : decode_any W_98750 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_98754 : bv 32 := 0x07813483.
Lemma F_98754 : fetch_word AsanUbsan.M.loaded_segments (0x9879c : word) = Some W_98754.
Proof. vm_refl. Qed.
Lemma D_98754 : decode_any W_98754 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_98758 : bv 32 := 0x07013903.
Lemma F_98758 : fetch_word AsanUbsan.M.loaded_segments (0x987a0 : word) = Some W_98758.
Proof. vm_refl. Qed.
Lemma D_98758 : decode_any W_98758 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_9875c : bv 32 := 0x06813983.
Lemma F_9875c : fetch_word AsanUbsan.M.loaded_segments (0x987a4 : word) = Some W_9875c.
Proof. vm_refl. Qed.
Lemma D_9875c : decode_any W_9875c = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_98760 : bv 32 := 0x06013a03.
Lemma F_98760 : fetch_word AsanUbsan.M.loaded_segments (0x987a8 : word) = Some W_98760.
Proof. vm_refl. Qed.
Lemma D_98760 : decode_any W_98760 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_98764 : bv 32 := 0x05813a83.
Lemma F_98764 : fetch_word AsanUbsan.M.loaded_segments (0x987ac : word) = Some W_98764.
Proof. vm_refl. Qed.
Lemma D_98764 : decode_any W_98764 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_98768 : bv 32 := 0x05013b03.
Lemma F_98768 : fetch_word AsanUbsan.M.loaded_segments (0x987b0 : word) = Some W_98768.
Proof. vm_refl. Qed.
Lemma D_98768 : decode_any W_98768 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9876c : bv 32 := 0x04813b83.
Lemma F_9876c : fetch_word AsanUbsan.M.loaded_segments (0x987b4 : word) = Some W_9876c.
Proof. vm_refl. Qed.
Lemma D_9876c : decode_any W_9876c = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_98770 : bv 32 := 0x04013c03.
Lemma F_98770 : fetch_word AsanUbsan.M.loaded_segments (0x987b8 : word) = Some W_98770.
Proof. vm_refl. Qed.
Lemma D_98770 : decode_any W_98770 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_98774 : bv 32 := 0x03813c83.
Lemma F_98774 : fetch_word AsanUbsan.M.loaded_segments (0x987bc : word) = Some W_98774.
Proof. vm_refl. Qed.
Lemma D_98774 : decode_any W_98774 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_98778 : bv 32 := 0x03013d03.
Lemma F_98778 : fetch_word AsanUbsan.M.loaded_segments (0x987c0 : word) = Some W_98778.
Proof. vm_refl. Qed.
Lemma D_98778 : decode_any W_98778 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9877c : bv 32 := 0x02813d83.
Lemma F_9877c : fetch_word AsanUbsan.M.loaded_segments (0x987c4 : word) = Some W_9877c.
Proof. vm_refl. Qed.
Lemma D_9877c : decode_any W_9877c = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_98780 : bv 32 := 0x09010113.
Lemma F_98780 : fetch_word AsanUbsan.M.loaded_segments (0x987c8 : word) = Some W_98780.
Proof. vm_refl. Qed.
Lemma D_98780 : decode_any W_98780 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_98784 : bv 32 := 0x00008067.
Lemma F_98784 : fetch_word AsanUbsan.M.loaded_segments (0x987cc : word) = Some W_98784.
Proof. vm_refl. Qed.
Lemma D_98784 : decode_any W_98784 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

