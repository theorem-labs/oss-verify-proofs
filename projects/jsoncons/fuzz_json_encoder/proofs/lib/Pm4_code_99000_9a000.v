(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_99570 : bv 32 := 0xf7010113.
Lemma F_99570 : fetch_word Asan.M.loaded_segments (0x995c0 : word) = Some W_99570.
Proof. vm_refl. Qed.
Lemma D_99570 : decode_any W_99570 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99574 : bv 32 := 0x08113423.
Lemma F_99574 : fetch_word Asan.M.loaded_segments (0x995c4 : word) = Some W_99574.
Proof. vm_refl. Qed.
Lemma D_99574 : decode_any W_99574 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99578 : bv 32 := 0x08813023.
Lemma F_99578 : fetch_word Asan.M.loaded_segments (0x995c8 : word) = Some W_99578.
Proof. vm_refl. Qed.
Lemma D_99578 : decode_any W_99578 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9957c : bv 32 := 0x06913c23.
Lemma F_9957c : fetch_word Asan.M.loaded_segments (0x995cc : word) = Some W_9957c.
Proof. vm_refl. Qed.
Lemma D_9957c : decode_any W_9957c = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99580 : bv 32 := 0x07213823.
Lemma F_99580 : fetch_word Asan.M.loaded_segments (0x995d0 : word) = Some W_99580.
Proof. vm_refl. Qed.
Lemma D_99580 : decode_any W_99580 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99584 : bv 32 := 0x07313423.
Lemma F_99584 : fetch_word Asan.M.loaded_segments (0x995d4 : word) = Some W_99584.
Proof. vm_refl. Qed.
Lemma D_99584 : decode_any W_99584 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99588 : bv 32 := 0x07413023.
Lemma F_99588 : fetch_word Asan.M.loaded_segments (0x995d8 : word) = Some W_99588.
Proof. vm_refl. Qed.
Lemma D_99588 : decode_any W_99588 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9958c : bv 32 := 0x05513c23.
Lemma F_9958c : fetch_word Asan.M.loaded_segments (0x995dc : word) = Some W_9958c.
Proof. vm_refl. Qed.
Lemma D_9958c : decode_any W_9958c = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99590 : bv 32 := 0x05613823.
Lemma F_99590 : fetch_word Asan.M.loaded_segments (0x995e0 : word) = Some W_99590.
Proof. vm_refl. Qed.
Lemma D_99590 : decode_any W_99590 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99594 : bv 32 := 0x05713423.
Lemma F_99594 : fetch_word Asan.M.loaded_segments (0x995e4 : word) = Some W_99594.
Proof. vm_refl. Qed.
Lemma D_99594 : decode_any W_99594 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99598 : bv 32 := 0x05813023.
Lemma F_99598 : fetch_word Asan.M.loaded_segments (0x995e8 : word) = Some W_99598.
Proof. vm_refl. Qed.
Lemma D_99598 : decode_any W_99598 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9959c : bv 32 := 0x03913c23.
Lemma F_9959c : fetch_word Asan.M.loaded_segments (0x995ec : word) = Some W_9959c.
Proof. vm_refl. Qed.
Lemma D_9959c : decode_any W_9959c = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995a0 : bv 32 := 0x03a13823.
Lemma F_995a0 : fetch_word Asan.M.loaded_segments (0x995f0 : word) = Some W_995a0.
Proof. vm_refl. Qed.
Lemma D_995a0 : decode_any W_995a0 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995a4 : bv 32 := 0x03b13423.
Lemma F_995a4 : fetch_word Asan.M.loaded_segments (0x995f4 : word) = Some W_995a4.
Proof. vm_refl. Qed.
Lemma D_995a4 : decode_any W_995a4 = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995a8 : bv 32 := 0x00058913.
Lemma F_995a8 : fetch_word Asan.M.loaded_segments (0x995f8 : word) = Some W_995a8.
Proof. vm_refl. Qed.
Lemma D_995a8 : decode_any W_995a8 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995ac : bv 32 := 0x000c7597.
Lemma F_995ac : fetch_word Asan.M.loaded_segments (0x995fc : word) = Some W_995ac.
Proof. vm_refl. Qed.
Lemma D_995ac : decode_any W_995ac = Some (Auipc 11 199, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995b0 : bv 32 := 0x60c5b583.
Lemma F_995b0 : fetch_word Asan.M.loaded_segments (0x99600 : word) = Some W_995b0.
Proof. vm_refl. Qed.
Lemma D_995b0 : decode_any W_995b0 = Some (Load SZ8 true 11 11 1548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995b4 : bv 32 := 0x0895c583.
Lemma F_995b4 : fetch_word Asan.M.loaded_segments (0x99604 : word) = Some W_995b4.
Proof. vm_refl. Qed.
Lemma D_995b4 : decode_any W_995b4 = Some (Load SZ1 false 11 11 137, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995b8 : bv 32 := 0x18058a63.
Lemma F_995b8 : fetch_word Asan.M.loaded_segments (0x99608 : word) = Some W_995b8.
Proof. vm_refl. Qed.
Lemma D_995b8 : decode_any W_995b8 = Some (Branch BC_EQ 11 0 404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995bc : bv 32 := 0x00050993.
Lemma F_995bc : fetch_word Asan.M.loaded_segments (0x9960c : word) = Some W_995bc.
Proof. vm_refl. Qed.
Lemma D_995bc : decode_any W_995bc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995c0 : bv 32 := 0x000c7517.
Lemma F_995c0 : fetch_word Asan.M.loaded_segments (0x99610 : word) = Some W_995c0.
Proof. vm_refl. Qed.
Lemma D_995c0 : decode_any W_995c0 = Some (Auipc 10 199, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995c4 : bv 32 := 0x65853d03.
Lemma F_995c4 : fetch_word Asan.M.loaded_segments (0x99614 : word) = Some W_995c4.
Proof. vm_refl. Qed.
Lemma D_995c4 : decode_any W_995c4 = Some (Load SZ8 true 26 10 1624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995c8 : bv 32 := 0x0009ba03.
Lemma F_995c8 : fetch_word Asan.M.loaded_segments (0x99618 : word) = Some W_995c8.
Proof. vm_refl. Qed.
Lemma D_995c8 : decode_any W_995c8 = Some (Load SZ8 true 20 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995cc : bv 32 := 0x000c8517.
Lemma F_995cc : fetch_word Asan.M.loaded_segments (0x9961c : word) = Some W_995cc.
Proof. vm_refl. Qed.
Lemma D_995cc : decode_any W_995cc = Some (Auipc 10 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995d0 : bv 32 := 0x000d2583.
Lemma F_995d0 : fetch_word Asan.M.loaded_segments (0x99620 : word) = Some W_995d0.
Proof. vm_refl. Qed.
Lemma D_995d0 : decode_any W_995d0 = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995d4 : bv 32 := 0x42c53a83.
Lemma F_995d4 : fetch_word Asan.M.loaded_segments (0x99624 : word) = Some W_995d4.
Proof. vm_refl. Qed.
Lemma D_995d4 : decode_any W_995d4 = Some (Load SZ8 true 21 10 1068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995d8 : bv 32 := 0x00300513.
Lemma F_995d8 : fetch_word Asan.M.loaded_segments (0x99628 : word) = Some W_995d8.
Proof. vm_refl. Qed.
Lemma D_995d8 : decode_any W_995d8 = Some (OpImm ALU_ADD 10 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995dc : bv 32 := 0x004a8ab3.
Lemma F_995dc : fetch_word Asan.M.loaded_segments (0x9962c : word) = Some W_995dc.
Proof. vm_refl. Qed.
Lemma D_995dc : decode_any W_995dc = Some (Op ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995e0 : bv 32 := 0x1ea5fa63.
Lemma F_995e0 : fetch_word Asan.M.loaded_segments (0x99630 : word) = Some W_995e0.
Proof. vm_refl. Qed.
Lemma D_995e0 : decode_any W_995e0 = Some (Branch BC_GEU 11 10 500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995e4 : bv 32 := 0x000abb03.
Lemma F_995e4 : fetch_word Asan.M.loaded_segments (0x99634 : word) = Some W_995e4.
Proof. vm_refl. Qed.
Lemma D_995e4 : decode_any W_995e4 = Some (Load SZ8 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995e8 : bv 32 := 0xfff00513.
Lemma F_995e8 : fetch_word Asan.M.loaded_segments (0x99638 : word) = Some W_995e8.
Proof. vm_refl. Qed.
Lemma D_995e8 : decode_any W_995e8 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995ec : bv 32 := 0x0230000f.
Lemma F_995ec : fetch_word Asan.M.loaded_segments (0x9963c : word) = Some W_995ec.
Proof. vm_refl. Qed.
Lemma D_995ec : decode_any W_995ec = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995f0 : bv 32 := 0x14ab0e63.
Lemma F_995f0 : fetch_word Asan.M.loaded_segments (0x99640 : word) = Some W_995f0.
Proof. vm_refl. Qed.
Lemma D_995f0 : decode_any W_995f0 = Some (Branch BC_EQ 22 10 348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995f4 : bv 32 := 0x080b1263.
Lemma F_995f4 : fetch_word Asan.M.loaded_segments (0x99644 : word) = Some W_995f4.
Proof. vm_refl. Qed.
Lemma D_995f4 : decode_any W_995f4 = Some (Branch BC_NE 22 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99678 : bv 32 := 0x0c0b0a63.
Lemma F_99678 : fetch_word Asan.M.loaded_segments (0x996c8 : word) = Some W_99678.
Proof. vm_refl. Qed.
Lemma D_99678 : decode_any W_99678 = Some (Branch BC_EQ 22 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9967c : bv 32 := 0x00c13823.
Lemma F_9967c : fetch_word Asan.M.loaded_segments (0x996cc : word) = Some W_9967c.
Proof. vm_refl. Qed.
Lemma D_9967c : decode_any W_9967c = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99680 : bv 32 := 0x00d13c23.
Lemma F_99680 : fetch_word Asan.M.loaded_segments (0x996d0 : word) = Some W_99680.
Proof. vm_refl. Qed.
Lemma D_99680 : decode_any W_99680 = Some (Store SZ8 2 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99684 : bv 32 := 0x0ff00513.
Lemma F_99684 : fetch_word Asan.M.loaded_segments (0x996d4 : word) = Some W_99684.
Proof. vm_refl. Qed.
Lemma D_99684 : decode_any W_99684 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99688 : bv 32 := 0x0aaa6863.
Lemma F_99688 : fetch_word Asan.M.loaded_segments (0x996d8 : word) = Some W_99688.
Proof. vm_refl. Qed.
Lemma D_99688 : decode_any W_99688 = Some (Branch BC_LTU 20 10 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99738 : bv 32 := 0x000b0513.
Lemma F_99738 : fetch_word Asan.M.loaded_segments (0x99788 : word) = Some W_99738.
Proof. vm_refl. Qed.
Lemma D_99738 : decode_any W_99738 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9973c : bv 32 := 0x004a1413.
Lemma F_9973c : fetch_word Asan.M.loaded_segments (0x9978c : word) = Some W_9973c.
Proof. vm_refl. Qed.
Lemma D_9973c : decode_any W_9973c = Some (ShiftImm ALU_SLL 8 20 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99740 : bv 32 := 0x00850433.
Lemma F_99740 : fetch_word Asan.M.loaded_segments (0x99790 : word) = Some W_99740.
Proof. vm_refl. Qed.
Lemma D_99740 : decode_any W_99740 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99744 : bv 32 := 0x00843503.
Lemma F_99744 : fetch_word Asan.M.loaded_segments (0x99794 : word) = Some W_99744.
Proof. vm_refl. Qed.
Lemma D_99744 : decode_any W_99744 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99748 : bv 32 := 0x04050263.
Lemma F_99748 : fetch_word Asan.M.loaded_segments (0x99798 : word) = Some W_99748.
Proof. vm_refl. Qed.
Lemma D_99748 : decode_any W_99748 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9974c : bv 32 := 0x00000513.
Lemma F_9974c : fetch_word Asan.M.loaded_segments (0x9979c : word) = Some W_9974c.
Proof. vm_refl. Qed.
Lemma D_9974c : decode_any W_9974c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99750 : bv 32 := 0x08813083.
Lemma F_99750 : fetch_word Asan.M.loaded_segments (0x997a0 : word) = Some W_99750.
Proof. vm_refl. Qed.
Lemma D_99750 : decode_any W_99750 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99754 : bv 32 := 0x08013403.
Lemma F_99754 : fetch_word Asan.M.loaded_segments (0x997a4 : word) = Some W_99754.
Proof. vm_refl. Qed.
Lemma D_99754 : decode_any W_99754 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99758 : bv 32 := 0x07813483.
Lemma F_99758 : fetch_word Asan.M.loaded_segments (0x997a8 : word) = Some W_99758.
Proof. vm_refl. Qed.
Lemma D_99758 : decode_any W_99758 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9975c : bv 32 := 0x07013903.
Lemma F_9975c : fetch_word Asan.M.loaded_segments (0x997ac : word) = Some W_9975c.
Proof. vm_refl. Qed.
Lemma D_9975c : decode_any W_9975c = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99760 : bv 32 := 0x06813983.
Lemma F_99760 : fetch_word Asan.M.loaded_segments (0x997b0 : word) = Some W_99760.
Proof. vm_refl. Qed.
Lemma D_99760 : decode_any W_99760 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99764 : bv 32 := 0x06013a03.
Lemma F_99764 : fetch_word Asan.M.loaded_segments (0x997b4 : word) = Some W_99764.
Proof. vm_refl. Qed.
Lemma D_99764 : decode_any W_99764 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99768 : bv 32 := 0x05813a83.
Lemma F_99768 : fetch_word Asan.M.loaded_segments (0x997b8 : word) = Some W_99768.
Proof. vm_refl. Qed.
Lemma D_99768 : decode_any W_99768 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9976c : bv 32 := 0x05013b03.
Lemma F_9976c : fetch_word Asan.M.loaded_segments (0x997bc : word) = Some W_9976c.
Proof. vm_refl. Qed.
Lemma D_9976c : decode_any W_9976c = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99770 : bv 32 := 0x04813b83.
Lemma F_99770 : fetch_word Asan.M.loaded_segments (0x997c0 : word) = Some W_99770.
Proof. vm_refl. Qed.
Lemma D_99770 : decode_any W_99770 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99774 : bv 32 := 0x04013c03.
Lemma F_99774 : fetch_word Asan.M.loaded_segments (0x997c4 : word) = Some W_99774.
Proof. vm_refl. Qed.
Lemma D_99774 : decode_any W_99774 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99778 : bv 32 := 0x03813c83.
Lemma F_99778 : fetch_word Asan.M.loaded_segments (0x997c8 : word) = Some W_99778.
Proof. vm_refl. Qed.
Lemma D_99778 : decode_any W_99778 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9977c : bv 32 := 0x03013d03.
Lemma F_9977c : fetch_word Asan.M.loaded_segments (0x997cc : word) = Some W_9977c.
Proof. vm_refl. Qed.
Lemma D_9977c : decode_any W_9977c = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99780 : bv 32 := 0x02813d83.
Lemma F_99780 : fetch_word Asan.M.loaded_segments (0x997d0 : word) = Some W_99780.
Proof. vm_refl. Qed.
Lemma D_99780 : decode_any W_99780 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99784 : bv 32 := 0x09010113.
Lemma F_99784 : fetch_word Asan.M.loaded_segments (0x997d4 : word) = Some W_99784.
Proof. vm_refl. Qed.
Lemma D_99784 : decode_any W_99784 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99788 : bv 32 := 0x00008067.
Lemma F_99788 : fetch_word Asan.M.loaded_segments (0x997d8 : word) = Some W_99788.
Proof. vm_refl. Qed.
Lemma D_99788 : decode_any W_99788 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

