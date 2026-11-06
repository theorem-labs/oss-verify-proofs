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

Definition W_95064 : bv 32 := 0x00060693.
Lemma F_95064 : fetch_word AsanUbsan.M.loaded_segments (0x950ac : word) = Some W_95064.
Proof. vm_refl. Qed.
Lemma D_95064 : decode_any W_95064 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_95068 : bv 32 := 0x00100613.
Lemma F_95068 : fetch_word AsanUbsan.M.loaded_segments (0x950b0 : word) = Some W_95068.
Proof. vm_refl. Qed.
Lemma D_95068 : decode_any W_95068 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9506c : bv 32 := 0xe81ff06f.
Lemma F_9506c : fetch_word AsanUbsan.M.loaded_segments (0x950b4 : word) = Some W_9506c.
Proof. vm_refl. Qed.
Lemma D_9506c : decode_any W_9506c = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.

Definition W_95580 : bv 32 := 0xef010113.
Lemma F_95580 : fetch_word AsanUbsan.M.loaded_segments (0x955c8 : word) = Some W_95580.
Proof. vm_refl. Qed.
Lemma D_95580 : decode_any W_95580 = Some (OpImm ALU_ADD 2 2 3824, 4%Z).
Proof. vm_refl. Qed.

Definition W_95584 : bv 32 := 0x10113423.
Lemma F_95584 : fetch_word AsanUbsan.M.loaded_segments (0x955cc : word) = Some W_95584.
Proof. vm_refl. Qed.
Lemma D_95584 : decode_any W_95584 = Some (Store SZ8 2 1 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_95588 : bv 32 := 0x10813023.
Lemma F_95588 : fetch_word AsanUbsan.M.loaded_segments (0x955d0 : word) = Some W_95588.
Proof. vm_refl. Qed.
Lemma D_95588 : decode_any W_95588 = Some (Store SZ8 2 8 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_9558c : bv 32 := 0x0e913c23.
Lemma F_9558c : fetch_word AsanUbsan.M.loaded_segments (0x955d4 : word) = Some W_9558c.
Proof. vm_refl. Qed.
Lemma D_9558c : decode_any W_9558c = Some (Store SZ8 2 9 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_95590 : bv 32 := 0x0f213823.
Lemma F_95590 : fetch_word AsanUbsan.M.loaded_segments (0x955d8 : word) = Some W_95590.
Proof. vm_refl. Qed.
Lemma D_95590 : decode_any W_95590 = Some (Store SZ8 2 18 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_95594 : bv 32 := 0x0f313423.
Lemma F_95594 : fetch_word AsanUbsan.M.loaded_segments (0x955dc : word) = Some W_95594.
Proof. vm_refl. Qed.
Lemma D_95594 : decode_any W_95594 = Some (Store SZ8 2 19 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_95598 : bv 32 := 0x0f413023.
Lemma F_95598 : fetch_word AsanUbsan.M.loaded_segments (0x955e0 : word) = Some W_95598.
Proof. vm_refl. Qed.
Lemma D_95598 : decode_any W_95598 = Some (Store SZ8 2 20 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_9559c : bv 32 := 0x0d513c23.
Lemma F_9559c : fetch_word AsanUbsan.M.loaded_segments (0x955e4 : word) = Some W_9559c.
Proof. vm_refl. Qed.
Lemma D_9559c : decode_any W_9559c = Some (Store SZ8 2 21 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_955a0 : bv 32 := 0x00050913.
Lemma F_955a0 : fetch_word AsanUbsan.M.loaded_segments (0x955e8 : word) = Some W_955a0.
Proof. vm_refl. Qed.
Lemma D_955a0 : decode_any W_955a0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_955a4 : bv 32 := 0xfff00513.
Lemma F_955a4 : fetch_word AsanUbsan.M.loaded_segments (0x955ec : word) = Some W_955a4.
Proof. vm_refl. Qed.
Lemma D_955a4 : decode_any W_955a4 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_955a8 : bv 32 := 0x12090463.
Lemma F_955a8 : fetch_word AsanUbsan.M.loaded_segments (0x955f0 : word) = Some W_955a8.
Proof. vm_refl. Qed.
Lemma D_955a8 : decode_any W_955a8 = Some (Branch BC_EQ 18 0 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_955ac : bv 32 := 0x00060413.
Lemma F_955ac : fetch_word AsanUbsan.M.loaded_segments (0x955f4 : word) = Some W_955ac.
Proof. vm_refl. Qed.
Lemma D_955ac : decode_any W_955ac = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_955b0 : bv 32 := 0x000bf617.
Lemma F_955b0 : fetch_word AsanUbsan.M.loaded_segments (0x955f8 : word) = Some W_955b0.
Proof. vm_refl. Qed.
Lemma D_955b0 : decode_any W_955b0 = Some (Auipc 12 191, 4%Z).
Proof. vm_refl. Qed.

Definition W_955b4 : bv 32 := 0xef863603.
Lemma F_955b4 : fetch_word AsanUbsan.M.loaded_segments (0x955fc : word) = Some W_955b4.
Proof. vm_refl. Qed.
Lemma D_955b4 : decode_any W_955b4 = Some (Load SZ8 true 12 12 3832, 4%Z).
Proof. vm_refl. Qed.

Definition W_955b8 : bv 32 := 0x10464603.
Lemma F_955b8 : fetch_word AsanUbsan.M.loaded_segments (0x95600 : word) = Some W_955b8.
Proof. vm_refl. Qed.
Lemma D_955b8 : decode_any W_955b8 = Some (Load SZ1 false 12 12 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_955bc : bv 32 := 0x00167613.
Lemma F_955bc : fetch_word AsanUbsan.M.loaded_segments (0x95604 : word) = Some W_955bc.
Proof. vm_refl. Qed.
Lemma D_955bc : decode_any W_955bc = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_955c0 : bv 32 := 0x10060863.
Lemma F_955c0 : fetch_word AsanUbsan.M.loaded_segments (0x95608 : word) = Some W_955c0.
Proof. vm_refl. Qed.
Lemma D_955c0 : decode_any W_955c0 = Some (Branch BC_EQ 12 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_956d0 : bv 32 := 0x0005051b.
Lemma F_956d0 : fetch_word AsanUbsan.M.loaded_segments (0x95718 : word) = Some W_956d0.
Proof. vm_refl. Qed.
Lemma D_956d0 : decode_any W_956d0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_956d4 : bv 32 := 0x10813083.
Lemma F_956d4 : fetch_word AsanUbsan.M.loaded_segments (0x9571c : word) = Some W_956d4.
Proof. vm_refl. Qed.
Lemma D_956d4 : decode_any W_956d4 = Some (Load SZ8 true 1 2 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_956d8 : bv 32 := 0x10013403.
Lemma F_956d8 : fetch_word AsanUbsan.M.loaded_segments (0x95720 : word) = Some W_956d8.
Proof. vm_refl. Qed.
Lemma D_956d8 : decode_any W_956d8 = Some (Load SZ8 true 8 2 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_956dc : bv 32 := 0x0f813483.
Lemma F_956dc : fetch_word AsanUbsan.M.loaded_segments (0x95724 : word) = Some W_956dc.
Proof. vm_refl. Qed.
Lemma D_956dc : decode_any W_956dc = Some (Load SZ8 true 9 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_956e0 : bv 32 := 0x0f013903.
Lemma F_956e0 : fetch_word AsanUbsan.M.loaded_segments (0x95728 : word) = Some W_956e0.
Proof. vm_refl. Qed.
Lemma D_956e0 : decode_any W_956e0 = Some (Load SZ8 true 18 2 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_956e4 : bv 32 := 0x0e813983.
Lemma F_956e4 : fetch_word AsanUbsan.M.loaded_segments (0x9572c : word) = Some W_956e4.
Proof. vm_refl. Qed.
Lemma D_956e4 : decode_any W_956e4 = Some (Load SZ8 true 19 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_956e8 : bv 32 := 0x0e013a03.
Lemma F_956e8 : fetch_word AsanUbsan.M.loaded_segments (0x95730 : word) = Some W_956e8.
Proof. vm_refl. Qed.
Lemma D_956e8 : decode_any W_956e8 = Some (Load SZ8 true 20 2 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_956ec : bv 32 := 0x0d813a83.
Lemma F_956ec : fetch_word AsanUbsan.M.loaded_segments (0x95734 : word) = Some W_956ec.
Proof. vm_refl. Qed.
Lemma D_956ec : decode_any W_956ec = Some (Load SZ8 true 21 2 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_956f0 : bv 32 := 0x11010113.
Lemma F_956f0 : fetch_word AsanUbsan.M.loaded_segments (0x95738 : word) = Some W_956f0.
Proof. vm_refl. Qed.
Lemma D_956f0 : decode_any W_956f0 = Some (OpImm ALU_ADD 2 2 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_956f4 : bv 32 := 0x00008067.
Lemma F_956f4 : fetch_word AsanUbsan.M.loaded_segments (0x9573c : word) = Some W_956f4.
Proof. vm_refl. Qed.
Lemma D_956f4 : decode_any W_956f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

