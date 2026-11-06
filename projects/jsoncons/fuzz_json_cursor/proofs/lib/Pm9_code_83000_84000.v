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

Definition W_83350 : bv 32 := 0xfb010113.
Lemma F_83350 : fetch_word AsanUbsan.M.loaded_segments (0x83398 : word) = Some W_83350.
Proof. vm_refl. Qed.
Lemma D_83350 : decode_any W_83350 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_83354 : bv 32 := 0x04113423.
Lemma F_83354 : fetch_word AsanUbsan.M.loaded_segments (0x8339c : word) = Some W_83354.
Proof. vm_refl. Qed.
Lemma D_83354 : decode_any W_83354 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_83358 : bv 32 := 0x04813023.
Lemma F_83358 : fetch_word AsanUbsan.M.loaded_segments (0x833a0 : word) = Some W_83358.
Proof. vm_refl. Qed.
Lemma D_83358 : decode_any W_83358 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8335c : bv 32 := 0x000d1517.
Lemma F_8335c : fetch_word AsanUbsan.M.loaded_segments (0x833a4 : word) = Some W_8335c.
Proof. vm_refl. Qed.
Lemma D_8335c : decode_any W_8335c = Some (Auipc 10 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_83360 : bv 32 := 0x19c53503.
Lemma F_83360 : fetch_word AsanUbsan.M.loaded_segments (0x833a8 : word) = Some W_83360.
Proof. vm_refl. Qed.
Lemma D_83360 : decode_any W_83360 = Some (Load SZ8 true 10 10 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_83364 : bv 32 := 0x0a051463.
Lemma F_83364 : fetch_word AsanUbsan.M.loaded_segments (0x833ac : word) = Some W_83364.
Proof. vm_refl. Qed.
Lemma D_83364 : decode_any W_83364 = Some (Branch BC_NE 10 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_8340c : bv 32 := 0x00000513.
Lemma F_8340c : fetch_word AsanUbsan.M.loaded_segments (0x83454 : word) = Some W_8340c.
Proof. vm_refl. Qed.
Lemma D_8340c : decode_any W_8340c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83410 : bv 32 := 0x04813083.
Lemma F_83410 : fetch_word AsanUbsan.M.loaded_segments (0x83458 : word) = Some W_83410.
Proof. vm_refl. Qed.
Lemma D_83410 : decode_any W_83410 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_83414 : bv 32 := 0x04013403.
Lemma F_83414 : fetch_word AsanUbsan.M.loaded_segments (0x8345c : word) = Some W_83414.
Proof. vm_refl. Qed.
Lemma D_83414 : decode_any W_83414 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_83418 : bv 32 := 0x05010113.
Lemma F_83418 : fetch_word AsanUbsan.M.loaded_segments (0x83460 : word) = Some W_83418.
Proof. vm_refl. Qed.
Lemma D_83418 : decode_any W_83418 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8341c : bv 32 := 0x00008067.
Lemma F_8341c : fetch_word AsanUbsan.M.loaded_segments (0x83464 : word) = Some W_8341c.
Proof. vm_refl. Qed.
Lemma D_8341c : decode_any W_8341c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_834bc : bv 32 := 0x000da517.
Lemma F_834bc : fetch_word AsanUbsan.M.loaded_segments (0x83504 : word) = Some W_834bc.
Proof. vm_refl. Qed.
Lemma D_834bc : decode_any W_834bc = Some (Auipc 10 218, 4%Z).
Proof. vm_refl. Qed.

Definition W_834c0 : bv 32 := 0x05c50513.
Lemma F_834c0 : fetch_word AsanUbsan.M.loaded_segments (0x83508 : word) = Some W_834c0.
Proof. vm_refl. Qed.
Lemma D_834c0 : decode_any W_834c0 = Some (OpImm ALU_ADD 10 10 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_834c4 : bv 32 := 0x00054583.
Lemma F_834c4 : fetch_word AsanUbsan.M.loaded_segments (0x8350c : word) = Some W_834c4.
Proof. vm_refl. Qed.
Lemma D_834c4 : decode_any W_834c4 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_834c8 : bv 32 := 0x00058663.
Lemma F_834c8 : fetch_word AsanUbsan.M.loaded_segments (0x83510 : word) = Some W_834c8.
Proof. vm_refl. Qed.
Lemma D_834c8 : decode_any W_834c8 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_834cc : bv 32 := 0x00452503.
Lemma F_834cc : fetch_word AsanUbsan.M.loaded_segments (0x83514 : word) = Some W_834cc.
Proof. vm_refl. Qed.
Lemma D_834cc : decode_any W_834cc = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_834d0 : bv 32 := 0x3d5c506f.
Lemma F_834d0 : fetch_word AsanUbsan.M.loaded_segments (0x83518 : word) = Some W_834d0.
Proof. vm_refl. Qed.
Lemma D_834d0 : decode_any W_834d0 = Some (Jal 0 809940, 4%Z).
Proof. vm_refl. Qed.

