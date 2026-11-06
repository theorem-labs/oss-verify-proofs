(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5f2fc : bv 32 := 0xfd010113.
Lemma F_5f2fc : fetch_word AsanUbsan.M.loaded_segments (0x5f344 : word) = Some W_5f2fc.
Proof. vm_refl. Qed.
Lemma D_5f2fc : decode_any W_5f2fc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f300 : bv 32 := 0x02113423.
Lemma F_5f300 : fetch_word AsanUbsan.M.loaded_segments (0x5f348 : word) = Some W_5f300.
Proof. vm_refl. Qed.
Lemma D_5f300 : decode_any W_5f300 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f304 : bv 32 := 0x02813023.
Lemma F_5f304 : fetch_word AsanUbsan.M.loaded_segments (0x5f34c : word) = Some W_5f304.
Proof. vm_refl. Qed.
Lemma D_5f304 : decode_any W_5f304 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f308 : bv 32 := 0x00913c23.
Lemma F_5f308 : fetch_word AsanUbsan.M.loaded_segments (0x5f350 : word) = Some W_5f308.
Proof. vm_refl. Qed.
Lemma D_5f308 : decode_any W_5f308 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f30c : bv 32 := 0x01213823.
Lemma F_5f30c : fetch_word AsanUbsan.M.loaded_segments (0x5f354 : word) = Some W_5f30c.
Proof. vm_refl. Qed.
Lemma D_5f30c : decode_any W_5f30c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f310 : bv 32 := 0x01313423.
Lemma F_5f310 : fetch_word AsanUbsan.M.loaded_segments (0x5f358 : word) = Some W_5f310.
Proof. vm_refl. Qed.
Lemma D_5f310 : decode_any W_5f310 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f314 : bv 32 := 0x01413023.
Lemma F_5f314 : fetch_word AsanUbsan.M.loaded_segments (0x5f35c : word) = Some W_5f314.
Proof. vm_refl. Qed.
Lemma D_5f314 : decode_any W_5f314 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f318 : bv 32 := 0x00058413.
Lemma F_5f318 : fetch_word AsanUbsan.M.loaded_segments (0x5f360 : word) = Some W_5f318.
Proof. vm_refl. Qed.
Lemma D_5f318 : decode_any W_5f318 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f31c : bv 32 := 0x00058583.
Lemma F_5f31c : fetch_word AsanUbsan.M.loaded_segments (0x5f364 : word) = Some W_5f31c.
Proof. vm_refl. Qed.
Lemma D_5f31c : decode_any W_5f31c = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f320 : bv 32 := 0x00300613.
Lemma F_5f320 : fetch_word AsanUbsan.M.loaded_segments (0x5f368 : word) = Some W_5f320.
Proof. vm_refl. Qed.
Lemma D_5f320 : decode_any W_5f320 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f324 : bv 32 := 0x12c59463.
Lemma F_5f324 : fetch_word AsanUbsan.M.loaded_segments (0x5f36c : word) = Some W_5f324.
Proof. vm_refl. Qed.
Lemma D_5f324 : decode_any W_5f324 = Some (Branch BC_NE 11 12 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f328 : bv 32 := 0x00068493.
Lemma F_5f328 : fetch_word AsanUbsan.M.loaded_segments (0x5f370 : word) = Some W_5f328.
Proof. vm_refl. Qed.
Lemma D_5f328 : decode_any W_5f328 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f32c : bv 32 := 0x00050913.
Lemma F_5f32c : fetch_word AsanUbsan.M.loaded_segments (0x5f374 : word) = Some W_5f32c.
Proof. vm_refl. Qed.
Lemma D_5f32c : decode_any W_5f32c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f330 : bv 32 := 0x3e82d0ef.
Lemma F_5f330 : fetch_word AsanUbsan.M.loaded_segments (0x5f378 : word) = Some W_5f330.
Proof. vm_refl. Qed.
Lemma D_5f330 : decode_any W_5f330 = Some (Jal 1 185320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f334 : bv 32 := 0x06050c63.
Lemma F_5f334 : fetch_word AsanUbsan.M.loaded_segments (0x5f37c : word) = Some W_5f334.
Proof. vm_refl. Qed.
Lemma D_5f334 : decode_any W_5f334 = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f338 : bv 32 := 0x00053683.
Lemma F_5f338 : fetch_word AsanUbsan.M.loaded_segments (0x5f380 : word) = Some W_5f338.
Proof. vm_refl. Qed.
Lemma D_5f338 : decode_any W_5f338 = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f33c : bv 32 := 0x0004b603.
Lemma F_5f33c : fetch_word AsanUbsan.M.loaded_segments (0x5f384 : word) = Some W_5f33c.
Proof. vm_refl. Qed.
Lemma D_5f33c : decode_any W_5f33c = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f340 : bv 32 := 0x0084b583.
Lemma F_5f340 : fetch_word AsanUbsan.M.loaded_segments (0x5f388 : word) = Some W_5f340.
Proof. vm_refl. Qed.
Lemma D_5f340 : decode_any W_5f340 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f344 : bv 32 := 0x0086a983.
Lemma F_5f344 : fetch_word AsanUbsan.M.loaded_segments (0x5f38c : word) = Some W_5f344.
Proof. vm_refl. Qed.
Lemma D_5f344 : decode_any W_5f344 = Some (Load SZ4 true 19 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f348 : bv 32 := 0x00050a13.
Lemma F_5f348 : fetch_word AsanUbsan.M.loaded_segments (0x5f390 : word) = Some W_5f348.
Proof. vm_refl. Qed.
Lemma D_5f348 : decode_any W_5f348 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f34c : bv 32 := 0x00060513.
Lemma F_5f34c : fetch_word AsanUbsan.M.loaded_segments (0x5f394 : word) = Some W_5f34c.
Proof. vm_refl. Qed.
Lemma D_5f34c : decode_any W_5f34c = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f350 : bv 32 := 0x2a9430ef.
Lemma F_5f350 : fetch_word AsanUbsan.M.loaded_segments (0x5f398 : word) = Some W_5f350.
Proof. vm_refl. Qed.
Lemma D_5f350 : decode_any W_5f350 = Some (Jal 1 277160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f354 : bv 32 := 0x02099993.
Lemma F_5f354 : fetch_word AsanUbsan.M.loaded_segments (0x5f39c : word) = Some W_5f354.
Proof. vm_refl. Qed.
Lemma D_5f354 : decode_any W_5f354 = Some (ShiftImm ALU_SLL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f358 : bv 32 := 0x02051513.
Lemma F_5f358 : fetch_word AsanUbsan.M.loaded_segments (0x5f3a0 : word) = Some W_5f358.
Proof. vm_refl. Qed.
Lemma D_5f358 : decode_any W_5f358 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f35c : bv 32 := 0x02055513.
Lemma F_5f35c : fetch_word AsanUbsan.M.loaded_segments (0x5f3a4 : word) = Some W_5f35c.
Proof. vm_refl. Qed.
Lemma D_5f35c : decode_any W_5f35c = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f360 : bv 32 := 0x00a9e533.
Lemma F_5f360 : fetch_word AsanUbsan.M.loaded_segments (0x5f3a8 : word) = Some W_5f360.
Proof. vm_refl. Qed.
Lemma D_5f360 : decode_any W_5f360 = Some (Op ALU_OR 10 19 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f364 : bv 32 := 0x00a43823.
Lemma F_5f364 : fetch_word AsanUbsan.M.loaded_segments (0x5f3ac : word) = Some W_5f364.
Proof. vm_refl. Qed.
Lemma D_5f364 : decode_any W_5f364 = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f368 : bv 32 := 0x050a0593.
Lemma F_5f368 : fetch_word AsanUbsan.M.loaded_segments (0x5f3b0 : word) = Some W_5f368.
Proof. vm_refl. Qed.
Lemma D_5f368 : decode_any W_5f368 = Some (OpImm ALU_ADD 11 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f36c : bv 32 := 0x00245683.
Lemma F_5f36c : fetch_word AsanUbsan.M.loaded_segments (0x5f3b4 : word) = Some W_5f36c.
Proof. vm_refl. Qed.
Lemma D_5f36c : decode_any W_5f36c = Some (Load SZ2 false 13 8 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f370 : bv 32 := 0x00446703.
Lemma F_5f370 : fetch_word AsanUbsan.M.loaded_segments (0x5f3b8 : word) = Some W_5f370.
Proof. vm_refl. Qed.
Lemma D_5f370 : decode_any W_5f370 = Some (Load SZ4 false 14 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f374 : bv 32 := 0x0d0a0613.
Lemma F_5f374 : fetch_word AsanUbsan.M.loaded_segments (0x5f3bc : word) = Some W_5f374.
Proof. vm_refl. Qed.
Lemma D_5f374 : decode_any W_5f374 = Some (OpImm ALU_ADD 12 20 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f378 : bv 32 := 0x2d890513.
Lemma F_5f378 : fetch_word AsanUbsan.M.loaded_segments (0x5f3c0 : word) = Some W_5f378.
Proof. vm_refl. Qed.
Lemma D_5f378 : decode_any W_5f378 = Some (OpImm ALU_ADD 10 18 728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f37c : bv 32 := 0x02069693.
Lemma F_5f37c : fetch_word AsanUbsan.M.loaded_segments (0x5f3c4 : word) = Some W_5f37c.
Proof. vm_refl. Qed.
Lemma D_5f37c : decode_any W_5f37c = Some (ShiftImm ALU_SLL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f380 : bv 32 := 0x00e6e7b3.
Lemma F_5f380 : fetch_word AsanUbsan.M.loaded_segments (0x5f3c8 : word) = Some W_5f380.
Proof. vm_refl. Qed.
Lemma D_5f380 : decode_any W_5f380 = Some (Op ALU_OR 15 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f384 : bv 32 := 0x00048693.
Lemma F_5f384 : fetch_word AsanUbsan.M.loaded_segments (0x5f3cc : word) = Some W_5f384.
Proof. vm_refl. Qed.
Lemma D_5f384 : decode_any W_5f384 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f388 : bv 32 := 0x00040713.
Lemma F_5f388 : fetch_word AsanUbsan.M.loaded_segments (0x5f3d0 : word) = Some W_5f388.
Proof. vm_refl. Qed.
Lemma D_5f388 : decode_any W_5f388 = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f38c : bv 32 := 0x02813083.
Lemma F_5f38c : fetch_word AsanUbsan.M.loaded_segments (0x5f3d4 : word) = Some W_5f38c.
Proof. vm_refl. Qed.
Lemma D_5f38c : decode_any W_5f38c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f390 : bv 32 := 0x02013403.
Lemma F_5f390 : fetch_word AsanUbsan.M.loaded_segments (0x5f3d8 : word) = Some W_5f390.
Proof. vm_refl. Qed.
Lemma D_5f390 : decode_any W_5f390 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f394 : bv 32 := 0x01813483.
Lemma F_5f394 : fetch_word AsanUbsan.M.loaded_segments (0x5f3dc : word) = Some W_5f394.
Proof. vm_refl. Qed.
Lemma D_5f394 : decode_any W_5f394 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f398 : bv 32 := 0x01013903.
Lemma F_5f398 : fetch_word AsanUbsan.M.loaded_segments (0x5f3e0 : word) = Some W_5f398.
Proof. vm_refl. Qed.
Lemma D_5f398 : decode_any W_5f398 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f39c : bv 32 := 0x00813983.
Lemma F_5f39c : fetch_word AsanUbsan.M.loaded_segments (0x5f3e4 : word) = Some W_5f39c.
Proof. vm_refl. Qed.
Lemma D_5f39c : decode_any W_5f39c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3a0 : bv 32 := 0x00013a03.
Lemma F_5f3a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f3e8 : word) = Some W_5f3a0.
Proof. vm_refl. Qed.
Lemma D_5f3a0 : decode_any W_5f3a0 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3a4 : bv 32 := 0x03010113.
Lemma F_5f3a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f3ec : word) = Some W_5f3a4.
Proof. vm_refl. Qed.
Lemma D_5f3a4 : decode_any W_5f3a4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3a8 : bv 32 := 0x0cc0006f.
Lemma F_5f3a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f3f0 : word) = Some W_5f3a8.
Proof. vm_refl. Qed.
Lemma D_5f3a8 : decode_any W_5f3a8 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f474 : bv 32 := 0xfb010113.
Lemma F_5f474 : fetch_word AsanUbsan.M.loaded_segments (0x5f4bc : word) = Some W_5f474.
Proof. vm_refl. Qed.
Lemma D_5f474 : decode_any W_5f474 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f478 : bv 32 := 0x04113423.
Lemma F_5f478 : fetch_word AsanUbsan.M.loaded_segments (0x5f4c0 : word) = Some W_5f478.
Proof. vm_refl. Qed.
Lemma D_5f478 : decode_any W_5f478 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f47c : bv 32 := 0x04813023.
Lemma F_5f47c : fetch_word AsanUbsan.M.loaded_segments (0x5f4c4 : word) = Some W_5f47c.
Proof. vm_refl. Qed.
Lemma D_5f47c : decode_any W_5f47c = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f480 : bv 32 := 0x02913c23.
Lemma F_5f480 : fetch_word AsanUbsan.M.loaded_segments (0x5f4c8 : word) = Some W_5f480.
Proof. vm_refl. Qed.
Lemma D_5f480 : decode_any W_5f480 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f484 : bv 32 := 0x03213823.
Lemma F_5f484 : fetch_word AsanUbsan.M.loaded_segments (0x5f4cc : word) = Some W_5f484.
Proof. vm_refl. Qed.
Lemma D_5f484 : decode_any W_5f484 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f488 : bv 32 := 0x03313423.
Lemma F_5f488 : fetch_word AsanUbsan.M.loaded_segments (0x5f4d0 : word) = Some W_5f488.
Proof. vm_refl. Qed.
Lemma D_5f488 : decode_any W_5f488 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f48c : bv 32 := 0x03413023.
Lemma F_5f48c : fetch_word AsanUbsan.M.loaded_segments (0x5f4d4 : word) = Some W_5f48c.
Proof. vm_refl. Qed.
Lemma D_5f48c : decode_any W_5f48c = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f490 : bv 32 := 0x01513c23.
Lemma F_5f490 : fetch_word AsanUbsan.M.loaded_segments (0x5f4d8 : word) = Some W_5f490.
Proof. vm_refl. Qed.
Lemma D_5f490 : decode_any W_5f490 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f494 : bv 32 := 0x01613823.
Lemma F_5f494 : fetch_word AsanUbsan.M.loaded_segments (0x5f4dc : word) = Some W_5f494.
Proof. vm_refl. Qed.
Lemma D_5f494 : decode_any W_5f494 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f498 : bv 32 := 0x00050413.
Lemma F_5f498 : fetch_word AsanUbsan.M.loaded_segments (0x5f4e0 : word) = Some W_5f498.
Proof. vm_refl. Qed.
Lemma D_5f498 : decode_any W_5f498 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f49c : bv 32 := 0x00c13023.
Lemma F_5f49c : fetch_word AsanUbsan.M.loaded_segments (0x5f4e4 : word) = Some W_5f49c.
Proof. vm_refl. Qed.
Lemma D_5f49c : decode_any W_5f49c = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4a0 : bv 32 := 0x00d13423.
Lemma F_5f4a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f4e8 : word) = Some W_5f4a0.
Proof. vm_refl. Qed.
Lemma D_5f4a0 : decode_any W_5f4a0 = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4a4 : bv 32 := 0x05053b03.
Lemma F_5f4a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f4ec : word) = Some W_5f4a4.
Proof. vm_refl. Qed.
Lemma D_5f4a4 : decode_any W_5f4a4 = Some (Load SZ8 true 22 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4a8 : bv 32 := 0x00058493.
Lemma F_5f4a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f4f0 : word) = Some W_5f4a8.
Proof. vm_refl. Qed.
Lemma D_5f4a8 : decode_any W_5f4a8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4ac : bv 32 := 0x000b0663.
Lemma F_5f4ac : fetch_word AsanUbsan.M.loaded_segments (0x5f4f4 : word) = Some W_5f4ac.
Proof. vm_refl. Qed.
Lemma D_5f4ac : decode_any W_5f4ac = Some (Branch BC_EQ 22 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4b0 : bv 32 := 0x04043503.
Lemma F_5f4b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f4f8 : word) = Some W_5f4b0.
Proof. vm_refl. Qed.
Lemma D_5f4b0 : decode_any W_5f4b0 = Some (Load SZ8 true 10 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4b4 : bv 32 := 0x0cf57263.
Lemma F_5f4b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f4fc : word) = Some W_5f4b4.
Proof. vm_refl. Qed.
Lemma D_5f4b4 : decode_any W_5f4b4 = Some (Branch BC_GEU 10 15 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f53c : bv 32 := 0x00013603.
Lemma F_5f53c : fetch_word AsanUbsan.M.loaded_segments (0x5f584 : word) = Some W_5f53c.
Proof. vm_refl. Qed.
Lemma D_5f53c : decode_any W_5f53c = Some (Load SZ8 true 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f540 : bv 32 := 0x00813683.
Lemma F_5f540 : fetch_word AsanUbsan.M.loaded_segments (0x5f588 : word) = Some W_5f540.
Proof. vm_refl. Qed.
Lemma D_5f540 : decode_any W_5f540 = Some (Load SZ8 true 13 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f544 : bv 32 := 0x00040513.
Lemma F_5f544 : fetch_word AsanUbsan.M.loaded_segments (0x5f58c : word) = Some W_5f544.
Proof. vm_refl. Qed.
Lemma D_5f544 : decode_any W_5f544 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f548 : bv 32 := 0x00048593.
Lemma F_5f548 : fetch_word AsanUbsan.M.loaded_segments (0x5f590 : word) = Some W_5f548.
Proof. vm_refl. Qed.
Lemma D_5f548 : decode_any W_5f548 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f54c : bv 32 := 0x831fd0ef.
Lemma F_5f54c : fetch_word AsanUbsan.M.loaded_segments (0x5f594 : word) = Some W_5f54c.
Proof. vm_refl. Qed.
Lemma D_5f54c : decode_any W_5f54c = Some (Jal 1 2086960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f550 : bv 32 := 0x04813083.
Lemma F_5f550 : fetch_word AsanUbsan.M.loaded_segments (0x5f598 : word) = Some W_5f550.
Proof. vm_refl. Qed.
Lemma D_5f550 : decode_any W_5f550 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f554 : bv 32 := 0x04013403.
Lemma F_5f554 : fetch_word AsanUbsan.M.loaded_segments (0x5f59c : word) = Some W_5f554.
Proof. vm_refl. Qed.
Lemma D_5f554 : decode_any W_5f554 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f558 : bv 32 := 0x03813483.
Lemma F_5f558 : fetch_word AsanUbsan.M.loaded_segments (0x5f5a0 : word) = Some W_5f558.
Proof. vm_refl. Qed.
Lemma D_5f558 : decode_any W_5f558 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f55c : bv 32 := 0x03013903.
Lemma F_5f55c : fetch_word AsanUbsan.M.loaded_segments (0x5f5a4 : word) = Some W_5f55c.
Proof. vm_refl. Qed.
Lemma D_5f55c : decode_any W_5f55c = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f560 : bv 32 := 0x02813983.
Lemma F_5f560 : fetch_word AsanUbsan.M.loaded_segments (0x5f5a8 : word) = Some W_5f560.
Proof. vm_refl. Qed.
Lemma D_5f560 : decode_any W_5f560 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f564 : bv 32 := 0x02013a03.
Lemma F_5f564 : fetch_word AsanUbsan.M.loaded_segments (0x5f5ac : word) = Some W_5f564.
Proof. vm_refl. Qed.
Lemma D_5f564 : decode_any W_5f564 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f568 : bv 32 := 0x01813a83.
Lemma F_5f568 : fetch_word AsanUbsan.M.loaded_segments (0x5f5b0 : word) = Some W_5f568.
Proof. vm_refl. Qed.
Lemma D_5f568 : decode_any W_5f568 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f56c : bv 32 := 0x01013b03.
Lemma F_5f56c : fetch_word AsanUbsan.M.loaded_segments (0x5f5b4 : word) = Some W_5f56c.
Proof. vm_refl. Qed.
Lemma D_5f56c : decode_any W_5f56c = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f570 : bv 32 := 0x05010113.
Lemma F_5f570 : fetch_word AsanUbsan.M.loaded_segments (0x5f5b8 : word) = Some W_5f570.
Proof. vm_refl. Qed.
Lemma D_5f570 : decode_any W_5f570 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f574 : bv 32 := 0x00008067.
Lemma F_5f574 : fetch_word AsanUbsan.M.loaded_segments (0x5f5bc : word) = Some W_5f574.
Proof. vm_refl. Qed.
Lemma D_5f574 : decode_any W_5f574 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f578 : bv 32 := 0x00060a13.
Lemma F_5f578 : fetch_word AsanUbsan.M.loaded_segments (0x5f5c0 : word) = Some W_5f578.
Proof. vm_refl. Qed.
Lemma D_5f578 : decode_any W_5f578 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f57c : bv 32 := 0x00068993.
Lemma F_5f57c : fetch_word AsanUbsan.M.loaded_segments (0x5f5c4 : word) = Some W_5f57c.
Proof. vm_refl. Qed.
Lemma D_5f57c : decode_any W_5f57c = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f580 : bv 32 := 0x00078913.
Lemma F_5f580 : fetch_word AsanUbsan.M.loaded_segments (0x5f5c8 : word) = Some W_5f580.
Proof. vm_refl. Qed.
Lemma D_5f580 : decode_any W_5f580 = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f584 : bv 32 := 0x00105517.
Lemma F_5f584 : fetch_word AsanUbsan.M.loaded_segments (0x5f5cc : word) = Some W_5f584.
Proof. vm_refl. Qed.
Lemma D_5f584 : decode_any W_5f584 = Some (Auipc 10 261, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f588 : bv 32 := 0xf4453583.
Lemma F_5f588 : fetch_word AsanUbsan.M.loaded_segments (0x5f5d0 : word) = Some W_5f588.
Proof. vm_refl. Qed.
Lemma D_5f588 : decode_any W_5f588 = Some (Load SZ8 true 11 10 3908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f58c : bv 32 := 0x0305a683.
Lemma F_5f58c : fetch_word AsanUbsan.M.loaded_segments (0x5f5d4 : word) = Some W_5f58c.
Proof. vm_refl. Qed.
Lemma D_5f58c : decode_any W_5f58c = Some (Load SZ4 true 13 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f590 : bv 32 := 0x04d05463.
Lemma F_5f590 : fetch_word AsanUbsan.M.loaded_segments (0x5f5d8 : word) = Some W_5f590.
Proof. vm_refl. Qed.
Lemma D_5f590 : decode_any W_5f590 = Some (Branch BC_GE 0 13 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f5d8 : bv 32 := 0x00275583.
Lemma F_5f5d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f620 : word) = Some W_5f5d8.
Proof. vm_refl. Qed.
Lemma D_5f5d8 : decode_any W_5f5d8 = Some (Load SZ2 false 11 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f5dc : bv 32 := 0x00476603.
Lemma F_5f5dc : fetch_word AsanUbsan.M.loaded_segments (0x5f624 : word) = Some W_5f5dc.
Proof. vm_refl. Qed.
Lemma D_5f5dc : decode_any W_5f5dc = Some (Load SZ4 false 12 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f5e0 : bv 32 := 0x01070513.
Lemma F_5f5e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f628 : word) = Some W_5f5e0.
Proof. vm_refl. Qed.
Lemma D_5f5e0 : decode_any W_5f5e0 = Some (OpImm ALU_ADD 10 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f5e4 : bv 32 := 0x02059593.
Lemma F_5f5e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f62c : word) = Some W_5f5e4.
Proof. vm_refl. Qed.
Lemma D_5f5e4 : decode_any W_5f5e4 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f5e8 : bv 32 := 0x00c5e5b3.
Lemma F_5f5e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f630 : word) = Some W_5f5e8.
Proof. vm_refl. Qed.
Lemma D_5f5e8 : decode_any W_5f5e8 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f5ec : bv 32 := 0x00758593.
Lemma F_5f5ec : fetch_word AsanUbsan.M.loaded_segments (0x5f634 : word) = Some W_5f5ec.
Proof. vm_refl. Qed.
Lemma D_5f5ec : decode_any W_5f5ec = Some (OpImm ALU_ADD 11 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f5f0 : bv 32 := 0xff85f593.
Lemma F_5f5f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f638 : word) = Some W_5f5f0.
Proof. vm_refl. Qed.
Lemma D_5f5f0 : decode_any W_5f5f0 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f5f4 : bv 32 := 0x0fd00613.
Lemma F_5f5f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f63c : word) = Some W_5f5f4.
Proof. vm_refl. Qed.
Lemma D_5f5f4 : decode_any W_5f5f4 = Some (OpImm ALU_ADD 12 0 253, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f5f8 : bv 32 := 0x00070a93.
Lemma F_5f5f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f640 : word) = Some W_5f5f8.
Proof. vm_refl. Qed.
Lemma D_5f5f8 : decode_any W_5f5f8 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f5fc : bv 32 := 0x370240ef.
Lemma F_5f5fc : fetch_word AsanUbsan.M.loaded_segments (0x5f644 : word) = Some W_5f5fc.
Proof. vm_refl. Qed.
Lemma D_5f5fc : decode_any W_5f5fc = Some (Jal 1 148336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f600 : bv 32 := 0x00048513.
Lemma F_5f600 : fetch_word AsanUbsan.M.loaded_segments (0x5f648 : word) = Some W_5f600.
Proof. vm_refl. Qed.
Lemma D_5f600 : decode_any W_5f600 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f604 : bv 32 := 0x000a0593.
Lemma F_5f604 : fetch_word AsanUbsan.M.loaded_segments (0x5f64c : word) = Some W_5f604.
Proof. vm_refl. Qed.
Lemma D_5f604 : decode_any W_5f604 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f608 : bv 32 := 0x00098613.
Lemma F_5f608 : fetch_word AsanUbsan.M.loaded_segments (0x5f650 : word) = Some W_5f608.
Proof. vm_refl. Qed.
Lemma D_5f608 : decode_any W_5f608 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f60c : bv 32 := 0x000a8693.
Lemma F_5f60c : fetch_word AsanUbsan.M.loaded_segments (0x5f654 : word) = Some W_5f60c.
Proof. vm_refl. Qed.
Lemma D_5f60c : decode_any W_5f60c = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f610 : bv 32 := 0x00090713.
Lemma F_5f610 : fetch_word AsanUbsan.M.loaded_segments (0x5f658 : word) = Some W_5f610.
Proof. vm_refl. Qed.
Lemma D_5f610 : decode_any W_5f610 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f614 : bv 32 := 0x010000ef.
Lemma F_5f614 : fetch_word AsanUbsan.M.loaded_segments (0x5f65c : word) = Some W_5f614.
Proof. vm_refl. Qed.
Lemma D_5f614 : decode_any W_5f614 = Some (Jal 1 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f618 : bv 32 := 0x0184b503.
Lemma F_5f618 : fetch_word AsanUbsan.M.loaded_segments (0x5f660 : word) = Some W_5f618.
Proof. vm_refl. Qed.
Lemma D_5f618 : decode_any W_5f618 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f61c : bv 32 := 0xf2ab60e3.
Lemma F_5f61c : fetch_word AsanUbsan.M.loaded_segments (0x5f664 : word) = Some W_5f61c.
Proof. vm_refl. Qed.
Lemma D_5f61c : decode_any W_5f61c = Some (Branch BC_LTU 22 10 7968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f620 : bv 32 := 0xf31ff06f.
Lemma F_5f620 : fetch_word AsanUbsan.M.loaded_segments (0x5f668 : word) = Some W_5f620.
Proof. vm_refl. Qed.
Lemma D_5f620 : decode_any W_5f620 = Some (Jal 0 2096944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f624 : bv 32 := 0xfc010113.
Lemma F_5f624 : fetch_word AsanUbsan.M.loaded_segments (0x5f66c : word) = Some W_5f624.
Proof. vm_refl. Qed.
Lemma D_5f624 : decode_any W_5f624 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f628 : bv 32 := 0x02113c23.
Lemma F_5f628 : fetch_word AsanUbsan.M.loaded_segments (0x5f670 : word) = Some W_5f628.
Proof. vm_refl. Qed.
Lemma D_5f628 : decode_any W_5f628 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f62c : bv 32 := 0x02813823.
Lemma F_5f62c : fetch_word AsanUbsan.M.loaded_segments (0x5f674 : word) = Some W_5f62c.
Proof. vm_refl. Qed.
Lemma D_5f62c : decode_any W_5f62c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f630 : bv 32 := 0x02913423.
Lemma F_5f630 : fetch_word AsanUbsan.M.loaded_segments (0x5f678 : word) = Some W_5f630.
Proof. vm_refl. Qed.
Lemma D_5f630 : decode_any W_5f630 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f634 : bv 32 := 0x03213023.
Lemma F_5f634 : fetch_word AsanUbsan.M.loaded_segments (0x5f67c : word) = Some W_5f634.
Proof. vm_refl. Qed.
Lemma D_5f634 : decode_any W_5f634 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f638 : bv 32 := 0x01313c23.
Lemma F_5f638 : fetch_word AsanUbsan.M.loaded_segments (0x5f680 : word) = Some W_5f638.
Proof. vm_refl. Qed.
Lemma D_5f638 : decode_any W_5f638 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f63c : bv 32 := 0x01413823.
Lemma F_5f63c : fetch_word AsanUbsan.M.loaded_segments (0x5f684 : word) = Some W_5f63c.
Proof. vm_refl. Qed.
Lemma D_5f63c : decode_any W_5f63c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f640 : bv 32 := 0x01513423.
Lemma F_5f640 : fetch_word AsanUbsan.M.loaded_segments (0x5f688 : word) = Some W_5f640.
Proof. vm_refl. Qed.
Lemma D_5f640 : decode_any W_5f640 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f644 : bv 32 := 0x00053783.
Lemma F_5f644 : fetch_word AsanUbsan.M.loaded_segments (0x5f68c : word) = Some W_5f644.
Proof. vm_refl. Qed.
Lemma D_5f644 : decode_any W_5f644 = Some (Load SZ8 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f648 : bv 32 := 0x00078a63.
Lemma F_5f648 : fetch_word AsanUbsan.M.loaded_segments (0x5f690 : word) = Some W_5f648.
Proof. vm_refl. Qed.
Lemma D_5f648 : decode_any W_5f648 = Some (Branch BC_EQ 15 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f64c : bv 32 := 0x01053803.
Lemma F_5f64c : fetch_word AsanUbsan.M.loaded_segments (0x5f694 : word) = Some W_5f64c.
Proof. vm_refl. Qed.
Lemma D_5f64c : decode_any W_5f64c = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f650 : bv 32 := 0x01083783.
Lemma F_5f650 : fetch_word AsanUbsan.M.loaded_segments (0x5f698 : word) = Some W_5f650.
Proof. vm_refl. Qed.
Lemma D_5f650 : decode_any W_5f650 = Some (Load SZ8 true 15 16 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f654 : bv 32 := 0x3fd00893.
Lemma F_5f654 : fetch_word AsanUbsan.M.loaded_segments (0x5f69c : word) = Some W_5f654.
Proof. vm_refl. Qed.
Lemma D_5f654 : decode_any W_5f654 = Some (OpImm ALU_ADD 17 0 1021, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f658 : bv 32 := 0x09179463.
Lemma F_5f658 : fetch_word AsanUbsan.M.loaded_segments (0x5f6a0 : word) = Some W_5f658.
Proof. vm_refl. Qed.
Lemma D_5f658 : decode_any W_5f658 = Some (Branch BC_NE 15 17 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f65c : bv 32 := 0x7805a783.
Lemma F_5f65c : fetch_word AsanUbsan.M.loaded_segments (0x5f6a4 : word) = Some W_5f65c.
Proof. vm_refl. Qed.
Lemma D_5f65c : decode_any W_5f65c = Some (Load SZ4 true 15 11 1920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f660 : bv 32 := 0x0e078263.
Lemma F_5f660 : fetch_word AsanUbsan.M.loaded_segments (0x5f6a8 : word) = Some W_5f660.
Proof. vm_refl. Qed.
Lemma D_5f660 : decode_any W_5f660 = Some (Branch BC_EQ 15 0 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f664 : bv 32 := 0xfff78793.
Lemma F_5f664 : fetch_word AsanUbsan.M.loaded_segments (0x5f6ac : word) = Some W_5f664.
Proof. vm_refl. Qed.
Lemma D_5f664 : decode_any W_5f664 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f668 : bv 32 := 0x02079813.
Lemma F_5f668 : fetch_word AsanUbsan.M.loaded_segments (0x5f6b0 : word) = Some W_5f668.
Proof. vm_refl. Qed.
Lemma D_5f668 : decode_any W_5f668 = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f66c : bv 32 := 0x78f5a023.
Lemma F_5f66c : fetch_word AsanUbsan.M.loaded_segments (0x5f6b4 : word) = Some W_5f66c.
Proof. vm_refl. Qed.
Lemma D_5f66c : decode_any W_5f66c = Some (Store SZ4 11 15 1920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f670 : bv 32 := 0x01e85793.
Lemma F_5f670 : fetch_word AsanUbsan.M.loaded_segments (0x5f6b8 : word) = Some W_5f670.
Proof. vm_refl. Qed.
Lemma D_5f670 : decode_any W_5f670 = Some (ShiftImm ALU_SRL 15 16 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f674 : bv 32 := 0x00f587b3.
Lemma F_5f674 : fetch_word AsanUbsan.M.loaded_segments (0x5f6bc : word) = Some W_5f674.
Proof. vm_refl. Qed.
Lemma D_5f674 : decode_any W_5f674 = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f678 : bv 32 := 0x7885b803.
Lemma F_5f678 : fetch_word AsanUbsan.M.loaded_segments (0x5f6c0 : word) = Some W_5f678.
Proof. vm_refl. Qed.
Lemma D_5f678 : decode_any W_5f678 = Some (Load SZ8 true 16 11 1928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f67c : bv 32 := 0x7ff58593.
Lemma F_5f67c : fetch_word AsanUbsan.M.loaded_segments (0x5f6c4 : word) = Some W_5f67c.
Proof. vm_refl. Qed.
Lemma D_5f67c : decode_any W_5f67c = Some (OpImm ALU_ADD 11 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f680 : bv 32 := 0x21158593.
Lemma F_5f680 : fetch_word AsanUbsan.M.loaded_segments (0x5f6c8 : word) = Some W_5f680.
Proof. vm_refl. Qed.
Lemma D_5f680 : decode_any W_5f680 = Some (OpImm ALU_ADD 11 11 529, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f684 : bv 32 := 0x7907e783.
Lemma F_5f684 : fetch_word AsanUbsan.M.loaded_segments (0x5f6cc : word) = Some W_5f684.
Proof. vm_refl. Qed.
Lemma D_5f684 : decode_any W_5f684 = Some (Load SZ4 false 15 15 1936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f688 : bv 32 := 0x0105b02f.
Lemma F_5f688 : fetch_word AsanUbsan.M.loaded_segments (0x5f6d0 : word) = Some W_5f688.
Proof. vm_refl. Qed.
Lemma D_5f688 : decode_any W_5f688 = Some (Amo AMO_ADD AD false false 0 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f68c : bv 32 := 0x0010b597.
Lemma F_5f68c : fetch_word AsanUbsan.M.loaded_segments (0x5f6d4 : word) = Some W_5f68c.
Proof. vm_refl. Qed.
Lemma D_5f68c : decode_any W_5f68c = Some (Auipc 11 267, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f690 : bv 32 := 0xaa45b583.
Lemma F_5f690 : fetch_word AsanUbsan.M.loaded_segments (0x5f6d8 : word) = Some W_5f690.
Proof. vm_refl. Qed.
Lemma D_5f690 : decode_any W_5f690 = Some (Load SZ8 true 11 11 2724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f694 : bv 32 := 0x00300813.
Lemma F_5f694 : fetch_word AsanUbsan.M.loaded_segments (0x5f6dc : word) = Some W_5f694.
Proof. vm_refl. Qed.
Lemma D_5f694 : decode_any W_5f694 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f698 : bv 32 := 0x00479793.
Lemma F_5f698 : fetch_word AsanUbsan.M.loaded_segments (0x5f6e0 : word) = Some W_5f698.
Proof. vm_refl. Qed.
Lemma D_5f698 : decode_any W_5f698 = Some (ShiftImm ALU_SLL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f69c : bv 32 := 0x02381813.
Lemma F_5f69c : fetch_word AsanUbsan.M.loaded_segments (0x5f6e4 : word) = Some W_5f69c.
Proof. vm_refl. Qed.
Lemma D_5f69c : decode_any W_5f69c = Some (ShiftImm ALU_SLL 16 16 35, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6a0 : bv 32 := 0x010585b3.
Lemma F_5f6a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f6e8 : word) = Some W_5f6a0.
Proof. vm_refl. Qed.
Lemma D_5f6a0 : decode_any W_5f6a0 = Some (Op ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6a4 : bv 32 := 0x00b785b3.
Lemma F_5f6a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f6ec : word) = Some W_5f6a4.
Proof. vm_refl. Qed.
Lemma D_5f6a4 : decode_any W_5f6a4 = Some (Op ALU_ADD 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6a8 : bv 32 := 0x0e058863.
Lemma F_5f6a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f6f0 : word) = Some W_5f6a8.
Proof. vm_refl. Qed.
Lemma D_5f6a8 : decode_any W_5f6a8 = Some (Branch BC_EQ 11 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6ac : bv 32 := 0x00100613.
Lemma F_5f6ac : fetch_word AsanUbsan.M.loaded_segments (0x5f6f4 : word) = Some W_5f6ac.
Proof. vm_refl. Qed.
Lemma D_5f6ac : decode_any W_5f6ac = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6b0 : bv 32 := 0x000027b7.
Lemma F_5f6b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f6f8 : word) = Some W_5f6b0.
Proof. vm_refl. Qed.
Lemma D_5f6b0 : decode_any W_5f6b0 = Some (Lui 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6b4 : bv 32 := 0x00f70733.
Lemma F_5f6b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f6fc : word) = Some W_5f6b4.
Proof. vm_refl. Qed.
Lemma D_5f6b4 : decode_any W_5f6b4 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6b8 : bv 32 := 0x00053783.
Lemma F_5f6b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f700 : word) = Some W_5f6b8.
Proof. vm_refl. Qed.
Lemma D_5f6b8 : decode_any W_5f6b8 = Some (Load SZ8 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6bc : bv 32 := 0x0005b023.
Lemma F_5f6bc : fetch_word AsanUbsan.M.loaded_segments (0x5f704 : word) = Some W_5f6bc.
Proof. vm_refl. Qed.
Lemma D_5f6bc : decode_any W_5f6bc = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6c0 : bv 32 := 0x00e5b423.
Lemma F_5f6c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f708 : word) = Some W_5f6c0.
Proof. vm_refl. Qed.
Lemma D_5f6c0 : decode_any W_5f6c0 = Some (Store SZ8 11 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6c4 : bv 32 := 0x00c5b823.
Lemma F_5f6c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f70c : word) = Some W_5f6c4.
Proof. vm_refl. Qed.
Lemma D_5f6c4 : decode_any W_5f6c4 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6c8 : bv 32 := 0x00d5bc23.
Lemma F_5f6c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f710 : word) = Some W_5f6c8.
Proof. vm_refl. Qed.
Lemma D_5f6c8 : decode_any W_5f6c8 = Some (Store SZ8 11 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6cc : bv 32 := 0x02078e63.
Lemma F_5f6cc : fetch_word AsanUbsan.M.loaded_segments (0x5f714 : word) = Some W_5f6cc.
Proof. vm_refl. Qed.
Lemma D_5f6cc : decode_any W_5f6cc = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6d0 : bv 32 := 0x01053603.
Lemma F_5f6d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f718 : word) = Some W_5f6d0.
Proof. vm_refl. Qed.
Lemma D_5f6d0 : decode_any W_5f6d0 = Some (Load SZ8 true 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6d4 : bv 32 := 0x00b63023.
Lemma F_5f6d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f71c : word) = Some W_5f6d4.
Proof. vm_refl. Qed.
Lemma D_5f6d4 : decode_any W_5f6d4 = Some (Store SZ8 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6d8 : bv 32 := 0x00178613.
Lemma F_5f6d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f720 : word) = Some W_5f6d8.
Proof. vm_refl. Qed.
Lemma D_5f6d8 : decode_any W_5f6d8 = Some (OpImm ALU_ADD 12 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6dc : bv 32 := 0x0300006f.
Lemma F_5f6dc : fetch_word AsanUbsan.M.loaded_segments (0x5f724 : word) = Some W_5f6dc.
Proof. vm_refl. Qed.
Lemma D_5f6dc : decode_any W_5f6dc = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6e0 : bv 32 := 0x0d17fc63.
Lemma F_5f6e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f728 : word) = Some W_5f6e0.
Proof. vm_refl. Qed.
Lemma D_5f6e0 : decode_any W_5f6e0 = Some (Branch BC_GEU 15 17 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6e4 : bv 32 := 0x00883583.
Lemma F_5f6e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f72c : word) = Some W_5f6e4.
Proof. vm_refl. Qed.
Lemma D_5f6e4 : decode_any W_5f6e4 = Some (Load SZ8 true 11 16 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6e8 : bv 32 := 0x00379613.
Lemma F_5f6e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f730 : word) = Some W_5f6e8.
Proof. vm_refl. Qed.
Lemma D_5f6e8 : decode_any W_5f6e8 = Some (ShiftImm ALU_SLL 12 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6ec : bv 32 := 0x00178793.
Lemma F_5f6ec : fetch_word AsanUbsan.M.loaded_segments (0x5f734 : word) = Some W_5f6ec.
Proof. vm_refl. Qed.
Lemma D_5f6ec : decode_any W_5f6ec = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6f0 : bv 32 := 0x00c80633.
Lemma F_5f6f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f738 : word) = Some W_5f6f0.
Proof. vm_refl. Qed.
Lemma D_5f6f0 : decode_any W_5f6f0 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6f4 : bv 32 := 0x00e585b3.
Lemma F_5f6f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f73c : word) = Some W_5f6f4.
Proof. vm_refl. Qed.
Lemma D_5f6f4 : decode_any W_5f6f4 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6f8 : bv 32 := 0x00b83423.
Lemma F_5f6f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f740 : word) = Some W_5f6f8.
Proof. vm_refl. Qed.
Lemma D_5f6f8 : decode_any W_5f6f8 = Some (Store SZ8 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6fc : bv 32 := 0x00f83823.
Lemma F_5f6fc : fetch_word AsanUbsan.M.loaded_segments (0x5f744 : word) = Some W_5f6fc.
Proof. vm_refl. Qed.
Lemma D_5f6fc : decode_any W_5f6fc = Some (Store SZ8 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f700 : bv 32 := 0x00d63c23.
Lemma F_5f700 : fetch_word AsanUbsan.M.loaded_segments (0x5f748 : word) = Some W_5f700.
Proof. vm_refl. Qed.
Lemma D_5f700 : decode_any W_5f700 = Some (Store SZ8 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f704 : bv 32 := 0x0100006f.
Lemma F_5f704 : fetch_word AsanUbsan.M.loaded_segments (0x5f74c : word) = Some W_5f704.
Proof. vm_refl. Qed.
Lemma D_5f704 : decode_any W_5f704 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f708 : bv 32 := 0x00b53423.
Lemma F_5f708 : fetch_word AsanUbsan.M.loaded_segments (0x5f750 : word) = Some W_5f708.
Proof. vm_refl. Qed.
Lemma D_5f708 : decode_any W_5f708 = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f70c : bv 32 := 0x00c53023.
Lemma F_5f70c : fetch_word AsanUbsan.M.loaded_segments (0x5f754 : word) = Some W_5f70c.
Proof. vm_refl. Qed.
Lemma D_5f70c : decode_any W_5f70c = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f710 : bv 32 := 0x00b53823.
Lemma F_5f710 : fetch_word AsanUbsan.M.loaded_segments (0x5f758 : word) = Some W_5f710.
Proof. vm_refl. Qed.
Lemma D_5f710 : decode_any W_5f710 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f714 : bv 32 := 0x01853583.
Lemma F_5f714 : fetch_word AsanUbsan.M.loaded_segments (0x5f75c : word) = Some W_5f714.
Proof. vm_refl. Qed.
Lemma D_5f714 : decode_any W_5f714 = Some (Load SZ8 true 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f718 : bv 32 := 0x00e585b3.
Lemma F_5f718 : fetch_word AsanUbsan.M.loaded_segments (0x5f760 : word) = Some W_5f718.
Proof. vm_refl. Qed.
Lemma D_5f718 : decode_any W_5f718 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f71c : bv 32 := 0x00b53c23.
Lemma F_5f71c : fetch_word AsanUbsan.M.loaded_segments (0x5f764 : word) = Some W_5f71c.
Proof. vm_refl. Qed.
Lemma D_5f71c : decode_any W_5f71c = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f720 : bv 32 := 0x03813083.
Lemma F_5f720 : fetch_word AsanUbsan.M.loaded_segments (0x5f768 : word) = Some W_5f720.
Proof. vm_refl. Qed.
Lemma D_5f720 : decode_any W_5f720 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f724 : bv 32 := 0x03013403.
Lemma F_5f724 : fetch_word AsanUbsan.M.loaded_segments (0x5f76c : word) = Some W_5f724.
Proof. vm_refl. Qed.
Lemma D_5f724 : decode_any W_5f724 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f728 : bv 32 := 0x02813483.
Lemma F_5f728 : fetch_word AsanUbsan.M.loaded_segments (0x5f770 : word) = Some W_5f728.
Proof. vm_refl. Qed.
Lemma D_5f728 : decode_any W_5f728 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f72c : bv 32 := 0x02013903.
Lemma F_5f72c : fetch_word AsanUbsan.M.loaded_segments (0x5f774 : word) = Some W_5f72c.
Proof. vm_refl. Qed.
Lemma D_5f72c : decode_any W_5f72c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f730 : bv 32 := 0x01813983.
Lemma F_5f730 : fetch_word AsanUbsan.M.loaded_segments (0x5f778 : word) = Some W_5f730.
Proof. vm_refl. Qed.
Lemma D_5f730 : decode_any W_5f730 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f734 : bv 32 := 0x01013a03.
Lemma F_5f734 : fetch_word AsanUbsan.M.loaded_segments (0x5f77c : word) = Some W_5f734.
Proof. vm_refl. Qed.
Lemma D_5f734 : decode_any W_5f734 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f738 : bv 32 := 0x00813a83.
Lemma F_5f738 : fetch_word AsanUbsan.M.loaded_segments (0x5f780 : word) = Some W_5f738.
Proof. vm_refl. Qed.
Lemma D_5f738 : decode_any W_5f738 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f73c : bv 32 := 0x04010113.
Lemma F_5f73c : fetch_word AsanUbsan.M.loaded_segments (0x5f784 : word) = Some W_5f73c.
Proof. vm_refl. Qed.
Lemma D_5f73c : decode_any W_5f73c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f740 : bv 32 := 0x00008067.
Lemma F_5f740 : fetch_word AsanUbsan.M.loaded_segments (0x5f788 : word) = Some W_5f740.
Proof. vm_refl. Qed.
Lemma D_5f740 : decode_any W_5f740 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f744 : bv 32 := 0x78058413.
Lemma F_5f744 : fetch_word AsanUbsan.M.loaded_segments (0x5f78c : word) = Some W_5f744.
Proof. vm_refl. Qed.
Lemma D_5f744 : decode_any W_5f744 = Some (OpImm ALU_ADD 8 11 1920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f748 : bv 32 := 0x0010b797.
Lemma F_5f748 : fetch_word AsanUbsan.M.loaded_segments (0x5f790 : word) = Some W_5f748.
Proof. vm_refl. Qed.
Lemma D_5f748 : decode_any W_5f748 = Some (Auipc 15 267, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f74c : bv 32 := 0x9c878793.
Lemma F_5f74c : fetch_word AsanUbsan.M.loaded_segments (0x5f794 : word) = Some W_5f74c.
Proof. vm_refl. Qed.
Lemma D_5f74c : decode_any W_5f74c = Some (OpImm ALU_ADD 15 15 2504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f750 : bv 32 := 0x00068913.
Lemma F_5f750 : fetch_word AsanUbsan.M.loaded_segments (0x5f798 : word) = Some W_5f750.
Proof. vm_refl. Qed.
Lemma D_5f750 : decode_any W_5f750 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f754 : bv 32 := 0x01800693.
Lemma F_5f754 : fetch_word AsanUbsan.M.loaded_segments (0x5f79c : word) = Some W_5f754.
Proof. vm_refl. Qed.
Lemma D_5f754 : decode_any W_5f754 = Some (OpImm ALU_ADD 13 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f758 : bv 32 := 0x00050993.
Lemma F_5f758 : fetch_word AsanUbsan.M.loaded_segments (0x5f7a0 : word) = Some W_5f758.
Proof. vm_refl. Qed.
Lemma D_5f758 : decode_any W_5f758 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f75c : bv 32 := 0x00058493.
Lemma F_5f75c : fetch_word AsanUbsan.M.loaded_segments (0x5f7a4 : word) = Some W_5f75c.
Proof. vm_refl. Qed.
Lemma D_5f75c : decode_any W_5f75c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f760 : bv 32 := 0x00058513.
Lemma F_5f760 : fetch_word AsanUbsan.M.loaded_segments (0x5f7a8 : word) = Some W_5f760.
Proof. vm_refl. Qed.
Lemma D_5f760 : decode_any W_5f760 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f764 : bv 32 := 0x00040593.
Lemma F_5f764 : fetch_word AsanUbsan.M.loaded_segments (0x5f7ac : word) = Some W_5f764.
Proof. vm_refl. Qed.
Lemma D_5f764 : decode_any W_5f764 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f768 : bv 32 := 0x00060a13.
Lemma F_5f768 : fetch_word AsanUbsan.M.loaded_segments (0x5f7b0 : word) = Some W_5f768.
Proof. vm_refl. Qed.
Lemma D_5f768 : decode_any W_5f768 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f76c : bv 32 := 0x00078613.
Lemma F_5f76c : fetch_word AsanUbsan.M.loaded_segments (0x5f7b4 : word) = Some W_5f76c.
Proof. vm_refl. Qed.
Lemma D_5f76c : decode_any W_5f76c = Some (OpImm ALU_ADD 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f770 : bv 32 := 0x00070a93.
Lemma F_5f770 : fetch_word AsanUbsan.M.loaded_segments (0x5f7b8 : word) = Some W_5f770.
Proof. vm_refl. Qed.
Lemma D_5f770 : decode_any W_5f770 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f774 : bv 32 := 0x7e4000ef.
Lemma F_5f774 : fetch_word AsanUbsan.M.loaded_segments (0x5f7bc : word) = Some W_5f774.
Proof. vm_refl. Qed.
Lemma D_5f774 : decode_any W_5f774 = Some (Jal 1 2020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f778 : bv 32 := 0x000a0613.
Lemma F_5f778 : fetch_word AsanUbsan.M.loaded_segments (0x5f7c0 : word) = Some W_5f778.
Proof. vm_refl. Qed.
Lemma D_5f778 : decode_any W_5f778 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f77c : bv 32 := 0x00050e63.
Lemma F_5f77c : fetch_word AsanUbsan.M.loaded_segments (0x5f7c4 : word) = Some W_5f77c.
Proof. vm_refl. Qed.
Lemma D_5f77c : decode_any W_5f77c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f780 : bv 32 := 0x00090693.
Lemma F_5f780 : fetch_word AsanUbsan.M.loaded_segments (0x5f7c8 : word) = Some W_5f780.
Proof. vm_refl. Qed.
Lemma D_5f780 : decode_any W_5f780 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f784 : bv 32 := 0x000a8713.
Lemma F_5f784 : fetch_word AsanUbsan.M.loaded_segments (0x5f7cc : word) = Some W_5f784.
Proof. vm_refl. Qed.
Lemma D_5f784 : decode_any W_5f784 = Some (OpImm ALU_ADD 14 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f788 : bv 32 := 0x00098513.
Lemma F_5f788 : fetch_word AsanUbsan.M.loaded_segments (0x5f7d0 : word) = Some W_5f788.
Proof. vm_refl. Qed.
Lemma D_5f788 : decode_any W_5f788 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f78c : bv 32 := 0x00042783.
Lemma F_5f78c : fetch_word AsanUbsan.M.loaded_segments (0x5f7d4 : word) = Some W_5f78c.
Proof. vm_refl. Qed.
Lemma D_5f78c : decode_any W_5f78c = Some (Load SZ4 true 15 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f790 : bv 32 := 0x00048593.
Lemma F_5f790 : fetch_word AsanUbsan.M.loaded_segments (0x5f7d8 : word) = Some W_5f790.
Proof. vm_refl. Qed.
Lemma D_5f790 : decode_any W_5f790 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f794 : bv 32 := 0xed1ff06f.
Lemma F_5f794 : fetch_word AsanUbsan.M.loaded_segments (0x5f7dc : word) = Some W_5f794.
Proof. vm_refl. Qed.
Lemma D_5f794 : decode_any W_5f794 = Some (Jal 0 2096848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f808 : bv 32 := 0xfd010113.
Lemma F_5f808 : fetch_word AsanUbsan.M.loaded_segments (0x5f850 : word) = Some W_5f808.
Proof. vm_refl. Qed.
Lemma D_5f808 : decode_any W_5f808 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f80c : bv 32 := 0x02113423.
Lemma F_5f80c : fetch_word AsanUbsan.M.loaded_segments (0x5f854 : word) = Some W_5f80c.
Proof. vm_refl. Qed.
Lemma D_5f80c : decode_any W_5f80c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f810 : bv 32 := 0x02813023.
Lemma F_5f810 : fetch_word AsanUbsan.M.loaded_segments (0x5f858 : word) = Some W_5f810.
Proof. vm_refl. Qed.
Lemma D_5f810 : decode_any W_5f810 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f814 : bv 32 := 0x00913c23.
Lemma F_5f814 : fetch_word AsanUbsan.M.loaded_segments (0x5f85c : word) = Some W_5f814.
Proof. vm_refl. Qed.
Lemma D_5f814 : decode_any W_5f814 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f818 : bv 32 := 0x01213823.
Lemma F_5f818 : fetch_word AsanUbsan.M.loaded_segments (0x5f860 : word) = Some W_5f818.
Proof. vm_refl. Qed.
Lemma D_5f818 : decode_any W_5f818 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f81c : bv 32 := 0x01313423.
Lemma F_5f81c : fetch_word AsanUbsan.M.loaded_segments (0x5f864 : word) = Some W_5f81c.
Proof. vm_refl. Qed.
Lemma D_5f81c : decode_any W_5f81c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f820 : bv 32 := 0x01413023.
Lemma F_5f820 : fetch_word AsanUbsan.M.loaded_segments (0x5f868 : word) = Some W_5f820.
Proof. vm_refl. Qed.
Lemma D_5f820 : decode_any W_5f820 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f824 : bv 32 := 0x00163713.
Lemma F_5f824 : fetch_word AsanUbsan.M.loaded_segments (0x5f86c : word) = Some W_5f824.
Proof. vm_refl. Qed.
Lemma D_5f824 : decode_any W_5f824 = Some (OpImm ALU_SLTU 14 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f828 : bv 32 := 0x00e60633.
Lemma F_5f828 : fetch_word AsanUbsan.M.loaded_segments (0x5f870 : word) = Some W_5f828.
Proof. vm_refl. Qed.
Lemma D_5f828 : decode_any W_5f828 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f82c : bv 32 := 0xfff64713.
Lemma F_5f82c : fetch_word AsanUbsan.M.loaded_segments (0x5f874 : word) = Some W_5f82c.
Proof. vm_refl. Qed.
Lemma D_5f82c : decode_any W_5f82c = Some (OpImm ALU_XOR 14 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f830 : bv 32 := 0x02d77263.
Lemma F_5f830 : fetch_word AsanUbsan.M.loaded_segments (0x5f878 : word) = Some W_5f830.
Proof. vm_refl. Qed.
Lemma D_5f830 : decode_any W_5f830 = Some (Branch BC_GEU 14 13 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f854 : bv 32 := 0x00900793.
Lemma F_5f854 : fetch_word AsanUbsan.M.loaded_segments (0x5f89c : word) = Some W_5f854.
Proof. vm_refl. Qed.
Lemma D_5f854 : decode_any W_5f854 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f858 : bv 32 := 0x00060713.
Lemma F_5f858 : fetch_word AsanUbsan.M.loaded_segments (0x5f8a0 : word) = Some W_5f858.
Proof. vm_refl. Qed.
Lemma D_5f858 : decode_any W_5f858 = Some (OpImm ALU_ADD 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f85c : bv 32 := 0x02f6e063.
Lemma F_5f85c : fetch_word AsanUbsan.M.loaded_segments (0x5f8a4 : word) = Some W_5f85c.
Proof. vm_refl. Qed.
Lemma D_5f85c : decode_any W_5f85c = Some (Branch BC_LTU 13 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f87c : bv 32 := 0x000107b7.
Lemma F_5f87c : fetch_word AsanUbsan.M.loaded_segments (0x5f8c4 : word) = Some W_5f87c.
Proof. vm_refl. Qed.
Lemma D_5f87c : decode_any W_5f87c = Some (Lui 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f880 : bv 32 := 0x00d7ee63.
Lemma F_5f880 : fetch_word AsanUbsan.M.loaded_segments (0x5f8c8 : word) = Some W_5f880.
Proof. vm_refl. Qed.
Lemma D_5f880 : decode_any W_5f880 = Some (Branch BC_LTU 15 13 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f884 : bv 32 := 0x00e7ec63.
Lemma F_5f884 : fetch_word AsanUbsan.M.loaded_segments (0x5f8cc : word) = Some W_5f884.
Proof. vm_refl. Qed.
Lemma D_5f884 : decode_any W_5f884 = Some (Branch BC_LTU 15 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f888 : bv 32 := 0x20000613.
Lemma F_5f888 : fetch_word AsanUbsan.M.loaded_segments (0x5f8d0 : word) = Some W_5f888.
Proof. vm_refl. Qed.
Lemma D_5f888 : decode_any W_5f888 = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f88c : bv 32 := 0x02e66a63.
Lemma F_5f88c : fetch_word AsanUbsan.M.loaded_segments (0x5f8d4 : word) = Some W_5f88c.
Proof. vm_refl. Qed.
Lemma D_5f88c : decode_any W_5f88c = Some (Branch BC_LTU 12 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f890 : bv 32 := 0x01f70713.
Lemma F_5f890 : fetch_word AsanUbsan.M.loaded_segments (0x5f8d8 : word) = Some W_5f890.
Proof. vm_refl. Qed.
Lemma D_5f890 : decode_any W_5f890 = Some (OpImm ALU_ADD 14 14 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f894 : bv 32 := 0x00575413.
Lemma F_5f894 : fetch_word AsanUbsan.M.loaded_segments (0x5f8dc : word) = Some W_5f894.
Proof. vm_refl. Qed.
Lemma D_5f894 : decode_any W_5f894 = Some (ShiftImm ALU_SRL 8 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f898 : bv 32 := 0x1040006f.
Lemma F_5f898 : fetch_word AsanUbsan.M.loaded_segments (0x5f8e0 : word) = Some W_5f898.
Proof. vm_refl. Qed.
Lemma D_5f898 : decode_any W_5f898 = Some (Jal 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f89c : bv 32 := 0x04050713.
Lemma F_5f89c : fetch_word AsanUbsan.M.loaded_segments (0x5f8e4 : word) = Some W_5f89c.
Proof. vm_refl. Qed.
Lemma D_5f89c : decode_any W_5f89c = Some (OpImm ALU_ADD 14 10 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8a0 : bv 32 := 0x2b050593.
Lemma F_5f8a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f8e8 : word) = Some W_5f8a0.
Proof. vm_refl. Qed.
Lemma D_5f8a0 : decode_any W_5f8a0 = Some (OpImm ALU_ADD 11 10 688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8a4 : bv 32 := 0x00070513.
Lemma F_5f8a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f8ec : word) = Some W_5f8a4.
Proof. vm_refl. Qed.
Lemma D_5f8a4 : decode_any W_5f8a4 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8a8 : bv 32 := 0x00068413.
Lemma F_5f8a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f8f0 : word) = Some W_5f8a8.
Proof. vm_refl. Qed.
Lemma D_5f8a8 : decode_any W_5f8a8 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8ac : bv 32 := 0x234000ef.
Lemma F_5f8ac : fetch_word AsanUbsan.M.loaded_segments (0x5f8f4 : word) = Some W_5f8ac.
Proof. vm_refl. Qed.
Lemma D_5f8ac : decode_any W_5f8ac = Some (Jal 1 564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8b0 : bv 32 := 0x00040693.
Lemma F_5f8b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f8f8 : word) = Some W_5f8b0.
Proof. vm_refl. Qed.
Lemma D_5f8b0 : decode_any W_5f8b0 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8b4 : bv 32 := 0x00900593.
Lemma F_5f8b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f8fc : word) = Some W_5f8b4.
Proof. vm_refl. Qed.
Lemma D_5f8b4 : decode_any W_5f8b4 = Some (OpImm ALU_ADD 11 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8b8 : bv 32 := 0x14b47463.
Lemma F_5f8b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f900 : word) = Some W_5f8b8.
Proof. vm_refl. Qed.
Lemma D_5f8b8 : decode_any W_5f8b8 = Some (Branch BC_GEU 8 11 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8bc : bv 32 := 0x1500006f.
Lemma F_5f8bc : fetch_word AsanUbsan.M.loaded_segments (0x5f904 : word) = Some W_5f8bc.
Proof. vm_refl. Qed.
Lemma D_5f8bc : decode_any W_5f8bc = Some (Jal 0 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8c0 : bv 32 := 0x00175613.
Lemma F_5f8c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f908 : word) = Some W_5f8c0.
Proof. vm_refl. Qed.
Lemma D_5f8c0 : decode_any W_5f8c0 = Some (ShiftImm ALU_SRL 12 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8c4 : bv 32 := 0x555557b7.
Lemma F_5f8c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f90c : word) = Some W_5f8c4.
Proof. vm_refl. Qed.
Lemma D_5f8c4 : decode_any W_5f8c4 = Some (Lui 15 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8c8 : bv 32 := 0x33333837.
Lemma F_5f8c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f910 : word) = Some W_5f8c8.
Proof. vm_refl. Qed.
Lemma D_5f8c8 : decode_any W_5f8c8 = Some (Lui 16 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8cc : bv 32 := 0x0f0f18b7.
Lemma F_5f8cc : fetch_word AsanUbsan.M.loaded_segments (0x5f914 : word) = Some W_5f8cc.
Proof. vm_refl. Qed.
Lemma D_5f8cc : decode_any W_5f8cc = Some (Lui 17 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8d0 : bv 32 := 0x010102b7.
Lemma F_5f8d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f918 : word) = Some W_5f8d0.
Proof. vm_refl. Qed.
Lemma D_5f8d0 : decode_any W_5f8d0 = Some (Lui 5 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8d4 : bv 32 := 0x00c76633.
Lemma F_5f8d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f91c : word) = Some W_5f8d4.
Proof. vm_refl. Qed.
Lemma D_5f8d4 : decode_any W_5f8d4 = Some (Op ALU_OR 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8d8 : bv 32 := 0x5557879b.
Lemma F_5f8d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f920 : word) = Some W_5f8d8.
Proof. vm_refl. Qed.
Lemma D_5f8d8 : decode_any W_5f8d8 = Some (OpImm32 15 15 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8dc : bv 32 := 0x3338081b.
Lemma F_5f8dc : fetch_word AsanUbsan.M.loaded_segments (0x5f924 : word) = Some W_5f8dc.
Proof. vm_refl. Qed.
Lemma D_5f8dc : decode_any W_5f8dc = Some (OpImm32 16 16 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8e0 : bv 32 := 0xf0f8889b.
Lemma F_5f8e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f928 : word) = Some W_5f8e0.
Proof. vm_refl. Qed.
Lemma D_5f8e0 : decode_any W_5f8e0 = Some (OpImm32 17 17 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8e4 : bv 32 := 0x1012829b.
Lemma F_5f8e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f92c : word) = Some W_5f8e4.
Proof. vm_refl. Qed.
Lemma D_5f8e4 : decode_any W_5f8e4 = Some (OpImm32 5 5 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8e8 : bv 32 := 0x00265313.
Lemma F_5f8e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f930 : word) = Some W_5f8e8.
Proof. vm_refl. Qed.
Lemma D_5f8e8 : decode_any W_5f8e8 = Some (ShiftImm ALU_SRL 6 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8ec : bv 32 := 0x00666633.
Lemma F_5f8ec : fetch_word AsanUbsan.M.loaded_segments (0x5f934 : word) = Some W_5f8ec.
Proof. vm_refl. Qed.
Lemma D_5f8ec : decode_any W_5f8ec = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8f0 : bv 32 := 0x02079313.
Lemma F_5f8f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f938 : word) = Some W_5f8f0.
Proof. vm_refl. Qed.
Lemma D_5f8f0 : decode_any W_5f8f0 = Some (ShiftImm ALU_SLL 6 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8f4 : bv 32 := 0x006787b3.
Lemma F_5f8f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f93c : word) = Some W_5f8f4.
Proof. vm_refl. Qed.
Lemma D_5f8f4 : decode_any W_5f8f4 = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8f8 : bv 32 := 0x02081313.
Lemma F_5f8f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f940 : word) = Some W_5f8f8.
Proof. vm_refl. Qed.
Lemma D_5f8f8 : decode_any W_5f8f8 = Some (ShiftImm ALU_SLL 6 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8fc : bv 32 := 0x00680833.
Lemma F_5f8fc : fetch_word AsanUbsan.M.loaded_segments (0x5f944 : word) = Some W_5f8fc.
Proof. vm_refl. Qed.
Lemma D_5f8fc : decode_any W_5f8fc = Some (Op ALU_ADD 16 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f900 : bv 32 := 0x02089313.
Lemma F_5f900 : fetch_word AsanUbsan.M.loaded_segments (0x5f948 : word) = Some W_5f900.
Proof. vm_refl. Qed.
Lemma D_5f900 : decode_any W_5f900 = Some (ShiftImm ALU_SLL 6 17 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f904 : bv 32 := 0x006888b3.
Lemma F_5f904 : fetch_word AsanUbsan.M.loaded_segments (0x5f94c : word) = Some W_5f904.
Proof. vm_refl. Qed.
Lemma D_5f904 : decode_any W_5f904 = Some (Op ALU_ADD 17 17 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f908 : bv 32 := 0x02029313.
Lemma F_5f908 : fetch_word AsanUbsan.M.loaded_segments (0x5f950 : word) = Some W_5f908.
Proof. vm_refl. Qed.
Lemma D_5f908 : decode_any W_5f908 = Some (ShiftImm ALU_SLL 6 5 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f90c : bv 32 := 0x006282b3.
Lemma F_5f90c : fetch_word AsanUbsan.M.loaded_segments (0x5f954 : word) = Some W_5f90c.
Proof. vm_refl. Qed.
Lemma D_5f90c : decode_any W_5f90c = Some (Op ALU_ADD 5 5 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f910 : bv 32 := 0x00465313.
Lemma F_5f910 : fetch_word AsanUbsan.M.loaded_segments (0x5f958 : word) = Some W_5f910.
Proof. vm_refl. Qed.
Lemma D_5f910 : decode_any W_5f910 = Some (ShiftImm ALU_SRL 6 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f914 : bv 32 := 0x00666633.
Lemma F_5f914 : fetch_word AsanUbsan.M.loaded_segments (0x5f95c : word) = Some W_5f914.
Proof. vm_refl. Qed.
Lemma D_5f914 : decode_any W_5f914 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f918 : bv 32 := 0x00865313.
Lemma F_5f918 : fetch_word AsanUbsan.M.loaded_segments (0x5f960 : word) = Some W_5f918.
Proof. vm_refl. Qed.
Lemma D_5f918 : decode_any W_5f918 = Some (ShiftImm ALU_SRL 6 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f91c : bv 32 := 0x00666633.
Lemma F_5f91c : fetch_word AsanUbsan.M.loaded_segments (0x5f964 : word) = Some W_5f91c.
Proof. vm_refl. Qed.
Lemma D_5f91c : decode_any W_5f91c = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f920 : bv 32 := 0x01065313.
Lemma F_5f920 : fetch_word AsanUbsan.M.loaded_segments (0x5f968 : word) = Some W_5f920.
Proof. vm_refl. Qed.
Lemma D_5f920 : decode_any W_5f920 = Some (ShiftImm ALU_SRL 6 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f924 : bv 32 := 0x00666633.
Lemma F_5f924 : fetch_word AsanUbsan.M.loaded_segments (0x5f96c : word) = Some W_5f924.
Proof. vm_refl. Qed.
Lemma D_5f924 : decode_any W_5f924 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f928 : bv 32 := 0x02065313.
Lemma F_5f928 : fetch_word AsanUbsan.M.loaded_segments (0x5f970 : word) = Some W_5f928.
Proof. vm_refl. Qed.
Lemma D_5f928 : decode_any W_5f928 = Some (ShiftImm ALU_SRL 6 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f92c : bv 32 := 0x00666633.
Lemma F_5f92c : fetch_word AsanUbsan.M.loaded_segments (0x5f974 : word) = Some W_5f92c.
Proof. vm_refl. Qed.
Lemma D_5f92c : decode_any W_5f92c = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f930 : bv 32 := 0xfff64613.
Lemma F_5f930 : fetch_word AsanUbsan.M.loaded_segments (0x5f978 : word) = Some W_5f930.
Proof. vm_refl. Qed.
Lemma D_5f930 : decode_any W_5f930 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f934 : bv 32 := 0x00165313.
Lemma F_5f934 : fetch_word AsanUbsan.M.loaded_segments (0x5f97c : word) = Some W_5f934.
Proof. vm_refl. Qed.
Lemma D_5f934 : decode_any W_5f934 = Some (ShiftImm ALU_SRL 6 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f938 : bv 32 := 0x00f377b3.
Lemma F_5f938 : fetch_word AsanUbsan.M.loaded_segments (0x5f980 : word) = Some W_5f938.
Proof. vm_refl. Qed.
Lemma D_5f938 : decode_any W_5f938 = Some (Op ALU_AND 15 6 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f93c : bv 32 := 0x40f60633.
Lemma F_5f93c : fetch_word AsanUbsan.M.loaded_segments (0x5f984 : word) = Some W_5f93c.
Proof. vm_refl. Qed.
Lemma D_5f93c : decode_any W_5f93c = Some (Op ALU_SUB 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f940 : bv 32 := 0x010677b3.
Lemma F_5f940 : fetch_word AsanUbsan.M.loaded_segments (0x5f988 : word) = Some W_5f940.
Proof. vm_refl. Qed.
Lemma D_5f940 : decode_any W_5f940 = Some (Op ALU_AND 15 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f944 : bv 32 := 0x00265613.
Lemma F_5f944 : fetch_word AsanUbsan.M.loaded_segments (0x5f98c : word) = Some W_5f944.
Proof. vm_refl. Qed.
Lemma D_5f944 : decode_any W_5f944 = Some (ShiftImm ALU_SRL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f948 : bv 32 := 0x01067633.
Lemma F_5f948 : fetch_word AsanUbsan.M.loaded_segments (0x5f990 : word) = Some W_5f948.
Proof. vm_refl. Qed.
Lemma D_5f948 : decode_any W_5f948 = Some (Op ALU_AND 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f94c : bv 32 := 0x00c78633.
Lemma F_5f94c : fetch_word AsanUbsan.M.loaded_segments (0x5f994 : word) = Some W_5f94c.
Proof. vm_refl. Qed.
Lemma D_5f94c : decode_any W_5f94c = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f950 : bv 32 := 0x00465793.
Lemma F_5f950 : fetch_word AsanUbsan.M.loaded_segments (0x5f998 : word) = Some W_5f950.
Proof. vm_refl. Qed.
Lemma D_5f950 : decode_any W_5f950 = Some (ShiftImm ALU_SRL 15 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f954 : bv 32 := 0x00f60633.
Lemma F_5f954 : fetch_word AsanUbsan.M.loaded_segments (0x5f99c : word) = Some W_5f954.
Proof. vm_refl. Qed.
Lemma D_5f954 : decode_any W_5f954 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f958 : bv 32 := 0x03e00793.
Lemma F_5f958 : fetch_word AsanUbsan.M.loaded_segments (0x5f9a0 : word) = Some W_5f958.
Proof. vm_refl. Qed.
Lemma D_5f958 : decode_any W_5f958 = Some (OpImm ALU_ADD 15 0 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f95c : bv 32 := 0x01167633.
Lemma F_5f95c : fetch_word AsanUbsan.M.loaded_segments (0x5f9a4 : word) = Some W_5f95c.
Proof. vm_refl. Qed.
Lemma D_5f95c : decode_any W_5f95c = Some (Op ALU_AND 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f960 : bv 32 := 0xfff00813.
Lemma F_5f960 : fetch_word AsanUbsan.M.loaded_segments (0x5f9a8 : word) = Some W_5f960.
Proof. vm_refl. Qed.
Lemma D_5f960 : decode_any W_5f960 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f964 : bv 32 := 0x02560633.
Lemma F_5f964 : fetch_word AsanUbsan.M.loaded_segments (0x5f9ac : word) = Some W_5f964.
Proof. vm_refl. Qed.
Lemma D_5f964 : decode_any W_5f964 = Some (Mul M_MUL 12 12 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f968 : bv 32 := 0x03865613.
Lemma F_5f968 : fetch_word AsanUbsan.M.loaded_segments (0x5f9b0 : word) = Some W_5f968.
Proof. vm_refl. Qed.
Lemma D_5f968 : decode_any W_5f968 = Some (ShiftImm ALU_SRL 12 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f96c : bv 32 := 0x40c787bb.
Lemma F_5f96c : fetch_word AsanUbsan.M.loaded_segments (0x5f9b4 : word) = Some W_5f96c.
Proof. vm_refl. Qed.
Lemma D_5f96c : decode_any W_5f96c = Some (Op32 ALU_SUB 15 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f970 : bv 32 := 0x00161613.
Lemma F_5f970 : fetch_word AsanUbsan.M.loaded_segments (0x5f9b8 : word) = Some W_5f970.
Proof. vm_refl. Qed.
Lemma D_5f970 : decode_any W_5f970 = Some (ShiftImm ALU_SLL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f974 : bv 32 := 0x00f758b3.
Lemma F_5f974 : fetch_word AsanUbsan.M.loaded_segments (0x5f9bc : word) = Some W_5f974.
Proof. vm_refl. Qed.
Lemma D_5f974 : decode_any W_5f974 = Some (Op ALU_SRL 17 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f978 : bv 32 := 0x00f817bb.
Lemma F_5f978 : fetch_word AsanUbsan.M.loaded_segments (0x5f9c0 : word) = Some W_5f978.
Proof. vm_refl. Qed.
Lemma D_5f978 : decode_any W_5f978 = Some (Op32 ALU_SLL 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f97c : bv 32 := 0x07e64613.
Lemma F_5f97c : fetch_word AsanUbsan.M.loaded_segments (0x5f9c4 : word) = Some W_5f97c.
Proof. vm_refl. Qed.
Lemma D_5f97c : decode_any W_5f97c = Some (OpImm ALU_XOR 12 12 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f980 : bv 32 := 0x0018f813.
Lemma F_5f980 : fetch_word AsanUbsan.M.loaded_segments (0x5f9c8 : word) = Some W_5f980.
Proof. vm_refl. Qed.
Lemma D_5f980 : decode_any W_5f980 = Some (OpImm ALU_AND 16 17 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f984 : bv 32 := 0xfff7c793.
Lemma F_5f984 : fetch_word AsanUbsan.M.loaded_segments (0x5f9cc : word) = Some W_5f984.
Proof. vm_refl. Qed.
Lemma D_5f984 : decode_any W_5f984 = Some (OpImm ALU_XOR 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f988 : bv 32 := 0x00f77733.
Lemma F_5f988 : fetch_word AsanUbsan.M.loaded_segments (0x5f9d0 : word) = Some W_5f988.
Proof. vm_refl. Qed.
Lemma D_5f988 : decode_any W_5f988 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f98c : bv 32 := 0x01066633.
Lemma F_5f98c : fetch_word AsanUbsan.M.loaded_segments (0x5f9d4 : word) = Some W_5f98c.
Proof. vm_refl. Qed.
Lemma D_5f98c : decode_any W_5f98c = Some (Op ALU_OR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f990 : bv 32 := 0x00e03733.
Lemma F_5f990 : fetch_word AsanUbsan.M.loaded_segments (0x5f9d8 : word) = Some W_5f990.
Proof. vm_refl. Qed.
Lemma D_5f990 : decode_any W_5f990 = Some (Op ALU_SLTU 14 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f994 : bv 32 := 0x00e60633.
Lemma F_5f994 : fetch_word AsanUbsan.M.loaded_segments (0x5f9dc : word) = Some W_5f994.
Proof. vm_refl. Qed.
Lemma D_5f994 : decode_any W_5f994 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f998 : bv 32 := 0xffe60413.
Lemma F_5f998 : fetch_word AsanUbsan.M.loaded_segments (0x5f9e0 : word) = Some W_5f998.
Proof. vm_refl. Qed.
Lemma D_5f998 : decode_any W_5f998 = Some (OpImm ALU_ADD 8 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f99c : bv 32 := 0x0a040063.
Lemma F_5f99c : fetch_word AsanUbsan.M.loaded_segments (0x5f9e4 : word) = Some W_5f99c.
Proof. vm_refl. Qed.
Lemma D_5f99c : decode_any W_5f99c = Some (Branch BC_EQ 8 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9a0 : bv 32 := 0x02000613.
Lemma F_5f9a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f9e8 : word) = Some W_5f9a0.
Proof. vm_refl. Qed.
Lemma D_5f9a0 : decode_any W_5f9a0 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9a4 : bv 32 := 0x0cc47a63.
Lemma F_5f9a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f9ec : word) = Some W_5f9a4.
Proof. vm_refl. Qed.
Lemma D_5f9a4 : decode_any W_5f9a4 = Some (Branch BC_GEU 8 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9a8 : bv 32 := 0x05000613.
Lemma F_5f9a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f9f0 : word) = Some W_5f9a8.
Proof. vm_refl. Qed.
Lemma D_5f9a8 : decode_any W_5f9a8 = Some (OpImm ALU_ADD 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9ac : bv 32 := 0x02c404b3.
Lemma F_5f9ac : fetch_word AsanUbsan.M.loaded_segments (0x5f9f4 : word) = Some W_5f9ac.
Proof. vm_refl. Qed.
Lemma D_5f9ac : decode_any W_5f9ac = Some (Mul M_MUL 9 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9b0 : bv 32 := 0x009584b3.
Lemma F_5f9b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f9f8 : word) = Some W_5f9b0.
Proof. vm_refl. Qed.
Lemma D_5f9b0 : decode_any W_5f9b0 = Some (Op ALU_ADD 9 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9b4 : bv 32 := 0x0004a603.
Lemma F_5f9b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f9fc : word) = Some W_5f9b4.
Proof. vm_refl. Qed.
Lemma D_5f9b4 : decode_any W_5f9b4 = Some (Load SZ4 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9b8 : bv 32 := 0x0e060063.
Lemma F_5f9b8 : fetch_word AsanUbsan.M.loaded_segments (0x5fa00 : word) = Some W_5f9b8.
Proof. vm_refl. Qed.
Lemma D_5f9b8 : decode_any W_5f9b8 = Some (Branch BC_EQ 12 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9bc : bv 32 := 0xfff60613.
Lemma F_5f9bc : fetch_word AsanUbsan.M.loaded_segments (0x5fa04 : word) = Some W_5f9bc.
Proof. vm_refl. Qed.
Lemma D_5f9bc : decode_any W_5f9bc = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9c0 : bv 32 := 0x7ff58593.
Lemma F_5f9c0 : fetch_word AsanUbsan.M.loaded_segments (0x5fa08 : word) = Some W_5f9c0.
Proof. vm_refl. Qed.
Lemma D_5f9c0 : decode_any W_5f9c0 = Some (OpImm ALU_ADD 11 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9c4 : bv 32 := 0x02061713.
Lemma F_5f9c4 : fetch_word AsanUbsan.M.loaded_segments (0x5fa0c : word) = Some W_5f9c4.
Proof. vm_refl. Qed.
Lemma D_5f9c4 : decode_any W_5f9c4 = Some (ShiftImm ALU_SLL 14 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9c8 : bv 32 := 0x00c4a023.
Lemma F_5f9c8 : fetch_word AsanUbsan.M.loaded_segments (0x5fa10 : word) = Some W_5f9c8.
Proof. vm_refl. Qed.
Lemma D_5f9c8 : decode_any W_5f9c8 = Some (Store SZ4 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9cc : bv 32 := 0x21158593.
Lemma F_5f9cc : fetch_word AsanUbsan.M.loaded_segments (0x5fa14 : word) = Some W_5f9cc.
Proof. vm_refl. Qed.
Lemma D_5f9cc : decode_any W_5f9cc = Some (OpImm ALU_ADD 11 11 529, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9d0 : bv 32 := 0x0084b603.
Lemma F_5f9d0 : fetch_word AsanUbsan.M.loaded_segments (0x5fa18 : word) = Some W_5f9d0.
Proof. vm_refl. Qed.
Lemma D_5f9d0 : decode_any W_5f9d0 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9d4 : bv 32 := 0x01e75713.
Lemma F_5f9d4 : fetch_word AsanUbsan.M.loaded_segments (0x5fa1c : word) = Some W_5f9d4.
Proof. vm_refl. Qed.
Lemma D_5f9d4 : decode_any W_5f9d4 = Some (ShiftImm ALU_SRL 14 14 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9d8 : bv 32 := 0x00e48733.
Lemma F_5f9d8 : fetch_word AsanUbsan.M.loaded_segments (0x5fa20 : word) = Some W_5f9d8.
Proof. vm_refl. Qed.
Lemma D_5f9d8 : decode_any W_5f9d8 = Some (Op ALU_ADD 14 9 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9dc : bv 32 := 0x01076703.
Lemma F_5f9dc : fetch_word AsanUbsan.M.loaded_segments (0x5fa24 : word) = Some W_5f9dc.
Proof. vm_refl. Qed.
Lemma D_5f9dc : decode_any W_5f9dc = Some (Load SZ4 false 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9e0 : bv 32 := 0x00c5b02f.
Lemma F_5f9e0 : fetch_word AsanUbsan.M.loaded_segments (0x5fa28 : word) = Some W_5f9e0.
Proof. vm_refl. Qed.
Lemma D_5f9e0 : decode_any W_5f9e0 = Some (Amo AMO_ADD AD false false 0 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9e4 : bv 32 := 0x02053503.
Lemma F_5f9e4 : fetch_word AsanUbsan.M.loaded_segments (0x5fa2c : word) = Some W_5f9e4.
Proof. vm_refl. Qed.
Lemma D_5f9e4 : decode_any W_5f9e4 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9e8 : bv 32 := 0x02041413.
Lemma F_5f9e8 : fetch_word AsanUbsan.M.loaded_segments (0x5fa30 : word) = Some W_5f9e8.
Proof. vm_refl. Qed.
Lemma D_5f9e8 : decode_any W_5f9e8 = Some (ShiftImm ALU_SLL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9ec : bv 32 := 0x00471713.
Lemma F_5f9ec : fetch_word AsanUbsan.M.loaded_segments (0x5fa34 : word) = Some W_5f9ec.
Proof. vm_refl. Qed.
Lemma D_5f9ec : decode_any W_5f9ec = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9f0 : bv 32 := 0x00a40533.
Lemma F_5f9f0 : fetch_word AsanUbsan.M.loaded_segments (0x5fa38 : word) = Some W_5f9f0.
Proof. vm_refl. Qed.
Lemma D_5f9f0 : decode_any W_5f9f0 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9f4 : bv 32 := 0x00a70533.
Lemma F_5f9f4 : fetch_word AsanUbsan.M.loaded_segments (0x5fa3c : word) = Some W_5f9f4.
Proof. vm_refl. Qed.
Lemma D_5f9f4 : decode_any W_5f9f4 = Some (Op ALU_ADD 10 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9f8 : bv 32 := 0x00900593.
Lemma F_5f9f8 : fetch_word AsanUbsan.M.loaded_segments (0x5fa40 : word) = Some W_5f9f8.
Proof. vm_refl. Qed.
Lemma D_5f9f8 : decode_any W_5f9f8 = Some (OpImm ALU_ADD 11 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9fc : bv 32 := 0x00b6e863.
Lemma F_5f9fc : fetch_word AsanUbsan.M.loaded_segments (0x5fa44 : word) = Some W_5f9fc.
Proof. vm_refl. Qed.
Lemma D_5f9fc : decode_any W_5f9fc = Some (Branch BC_LTU 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa00 : bv 32 := 0xfff68693.
Lemma F_5fa00 : fetch_word AsanUbsan.M.loaded_segments (0x5fa48 : word) = Some W_5fa00.
Proof. vm_refl. Qed.
Lemma D_5fa00 : decode_any W_5fa00 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa04 : bv 32 := 0x00a6f6b3.
Lemma F_5fa04 : fetch_word AsanUbsan.M.loaded_segments (0x5fa4c : word) = Some W_5fa04.
Proof. vm_refl. Qed.
Lemma D_5fa04 : decode_any W_5fa04 = Some (Op ALU_AND 13 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa08 : bv 32 := 0x04069a63.
Lemma F_5fa08 : fetch_word AsanUbsan.M.loaded_segments (0x5fa50 : word) = Some W_5fa08.
Proof. vm_refl. Qed.
Lemma D_5fa08 : decode_any W_5fa08 = Some (Branch BC_NE 13 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa0c : bv 32 := 0x02813083.
Lemma F_5fa0c : fetch_word AsanUbsan.M.loaded_segments (0x5fa54 : word) = Some W_5fa0c.
Proof. vm_refl. Qed.
Lemma D_5fa0c : decode_any W_5fa0c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa10 : bv 32 := 0x02013403.
Lemma F_5fa10 : fetch_word AsanUbsan.M.loaded_segments (0x5fa58 : word) = Some W_5fa10.
Proof. vm_refl. Qed.
Lemma D_5fa10 : decode_any W_5fa10 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa14 : bv 32 := 0x01813483.
Lemma F_5fa14 : fetch_word AsanUbsan.M.loaded_segments (0x5fa5c : word) = Some W_5fa14.
Proof. vm_refl. Qed.
Lemma D_5fa14 : decode_any W_5fa14 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa18 : bv 32 := 0x01013903.
Lemma F_5fa18 : fetch_word AsanUbsan.M.loaded_segments (0x5fa60 : word) = Some W_5fa18.
Proof. vm_refl. Qed.
Lemma D_5fa18 : decode_any W_5fa18 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa1c : bv 32 := 0x00813983.
Lemma F_5fa1c : fetch_word AsanUbsan.M.loaded_segments (0x5fa64 : word) = Some W_5fa1c.
Proof. vm_refl. Qed.
Lemma D_5fa1c : decode_any W_5fa1c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa20 : bv 32 := 0x00013a03.
Lemma F_5fa20 : fetch_word AsanUbsan.M.loaded_segments (0x5fa68 : word) = Some W_5fa20.
Proof. vm_refl. Qed.
Lemma D_5fa20 : decode_any W_5fa20 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa24 : bv 32 := 0x03010113.
Lemma F_5fa24 : fetch_word AsanUbsan.M.loaded_segments (0x5fa6c : word) = Some W_5fa24.
Proof. vm_refl. Qed.
Lemma D_5fa24 : decode_any W_5fa24 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa28 : bv 32 := 0x00008067.
Lemma F_5fa28 : fetch_word AsanUbsan.M.loaded_segments (0x5fa70 : word) = Some W_5fa28.
Proof. vm_refl. Qed.
Lemma D_5fa28 : decode_any W_5fa28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa98 : bv 32 := 0x00068913.
Lemma F_5fa98 : fetch_word AsanUbsan.M.loaded_segments (0x5fae0 : word) = Some W_5fa98.
Proof. vm_refl. Qed.
Lemma D_5fa98 : decode_any W_5fa98 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa9c : bv 32 := 0x00050613.
Lemma F_5fa9c : fetch_word AsanUbsan.M.loaded_segments (0x5fae4 : word) = Some W_5fa9c.
Proof. vm_refl. Qed.
Lemma D_5fa9c : decode_any W_5fa9c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faa0 : bv 32 := 0x00058993.
Lemma F_5faa0 : fetch_word AsanUbsan.M.loaded_segments (0x5fae8 : word) = Some W_5faa0.
Proof. vm_refl. Qed.
Lemma D_5faa0 : decode_any W_5faa0 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faa4 : bv 32 := 0x00058513.
Lemma F_5faa4 : fetch_word AsanUbsan.M.loaded_segments (0x5faec : word) = Some W_5faa4.
Proof. vm_refl. Qed.
Lemma D_5faa4 : decode_any W_5faa4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faa8 : bv 32 := 0x00048593.
Lemma F_5faa8 : fetch_word AsanUbsan.M.loaded_segments (0x5faf0 : word) = Some W_5faa8.
Proof. vm_refl. Qed.
Lemma D_5faa8 : decode_any W_5faa8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faac : bv 32 := 0x00060a13.
Lemma F_5faac : fetch_word AsanUbsan.M.loaded_segments (0x5faf4 : word) = Some W_5faac.
Proof. vm_refl. Qed.
Lemma D_5faac : decode_any W_5faac = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fab0 : bv 32 := 0x00040693.
Lemma F_5fab0 : fetch_word AsanUbsan.M.loaded_segments (0x5faf8 : word) = Some W_5fab0.
Proof. vm_refl. Qed.
Lemma D_5fab0 : decode_any W_5fab0 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fab4 : bv 32 := 0x4a4000ef.
Lemma F_5fab4 : fetch_word AsanUbsan.M.loaded_segments (0x5fafc : word) = Some W_5fab4.
Proof. vm_refl. Qed.
Lemma D_5fab4 : decode_any W_5fab4 = Some (Jal 1 1188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fab8 : bv 32 := 0x00050c63.
Lemma F_5fab8 : fetch_word AsanUbsan.M.loaded_segments (0x5fb00 : word) = Some W_5fab8.
Proof. vm_refl. Qed.
Lemma D_5fab8 : decode_any W_5fab8 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fabc : bv 32 := 0x0004a603.
Lemma F_5fabc : fetch_word AsanUbsan.M.loaded_segments (0x5fb04 : word) = Some W_5fabc.
Proof. vm_refl. Qed.
Lemma D_5fabc : decode_any W_5fabc = Some (Load SZ4 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fac0 : bv 32 := 0x00090693.
Lemma F_5fac0 : fetch_word AsanUbsan.M.loaded_segments (0x5fb08 : word) = Some W_5fac0.
Proof. vm_refl. Qed.
Lemma D_5fac0 : decode_any W_5fac0 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fac4 : bv 32 := 0x000a0513.
Lemma F_5fac4 : fetch_word AsanUbsan.M.loaded_segments (0x5fb0c : word) = Some W_5fac4.
Proof. vm_refl. Qed.
Lemma D_5fac4 : decode_any W_5fac4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fac8 : bv 32 := 0x00098593.
Lemma F_5fac8 : fetch_word AsanUbsan.M.loaded_segments (0x5fb10 : word) = Some W_5fac8.
Proof. vm_refl. Qed.
Lemma D_5fac8 : decode_any W_5fac8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5facc : bv 32 := 0xef1ff06f.
Lemma F_5facc : fetch_word AsanUbsan.M.loaded_segments (0x5fb14 : word) = Some W_5facc.
Proof. vm_refl. Qed.
Lemma D_5facc : decode_any W_5facc = Some (Jal 0 2096880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fae0 : bv 32 := 0xfa010113.
Lemma F_5fae0 : fetch_word AsanUbsan.M.loaded_segments (0x5fb28 : word) = Some W_5fae0.
Proof. vm_refl. Qed.
Lemma D_5fae0 : decode_any W_5fae0 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fae4 : bv 32 := 0x04113c23.
Lemma F_5fae4 : fetch_word AsanUbsan.M.loaded_segments (0x5fb2c : word) = Some W_5fae4.
Proof. vm_refl. Qed.
Lemma D_5fae4 : decode_any W_5fae4 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fae8 : bv 32 := 0x04813823.
Lemma F_5fae8 : fetch_word AsanUbsan.M.loaded_segments (0x5fb30 : word) = Some W_5fae8.
Proof. vm_refl. Qed.
Lemma D_5fae8 : decode_any W_5fae8 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faec : bv 32 := 0x04913423.
Lemma F_5faec : fetch_word AsanUbsan.M.loaded_segments (0x5fb34 : word) = Some W_5faec.
Proof. vm_refl. Qed.
Lemma D_5faec : decode_any W_5faec = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faf0 : bv 32 := 0x05213023.
Lemma F_5faf0 : fetch_word AsanUbsan.M.loaded_segments (0x5fb38 : word) = Some W_5faf0.
Proof. vm_refl. Qed.
Lemma D_5faf0 : decode_any W_5faf0 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faf4 : bv 32 := 0x03313c23.
Lemma F_5faf4 : fetch_word AsanUbsan.M.loaded_segments (0x5fb3c : word) = Some W_5faf4.
Proof. vm_refl. Qed.
Lemma D_5faf4 : decode_any W_5faf4 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faf8 : bv 32 := 0x03413823.
Lemma F_5faf8 : fetch_word AsanUbsan.M.loaded_segments (0x5fb40 : word) = Some W_5faf8.
Proof. vm_refl. Qed.
Lemma D_5faf8 : decode_any W_5faf8 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fafc : bv 32 := 0x03513423.
Lemma F_5fafc : fetch_word AsanUbsan.M.loaded_segments (0x5fb44 : word) = Some W_5fafc.
Proof. vm_refl. Qed.
Lemma D_5fafc : decode_any W_5fafc = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb00 : bv 32 := 0x03613023.
Lemma F_5fb00 : fetch_word AsanUbsan.M.loaded_segments (0x5fb48 : word) = Some W_5fb00.
Proof. vm_refl. Qed.
Lemma D_5fb00 : decode_any W_5fb00 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb04 : bv 32 := 0x01713c23.
Lemma F_5fb04 : fetch_word AsanUbsan.M.loaded_segments (0x5fb4c : word) = Some W_5fb04.
Proof. vm_refl. Qed.
Lemma D_5fb04 : decode_any W_5fb04 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb08 : bv 32 := 0x01813823.
Lemma F_5fb08 : fetch_word AsanUbsan.M.loaded_segments (0x5fb50 : word) = Some W_5fb08.
Proof. vm_refl. Qed.
Lemma D_5fb08 : decode_any W_5fb08 = Some (Store SZ8 2 24 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb0c : bv 32 := 0x01913423.
Lemma F_5fb0c : fetch_word AsanUbsan.M.loaded_segments (0x5fb54 : word) = Some W_5fb0c.
Proof. vm_refl. Qed.
Lemma D_5fb0c : decode_any W_5fb0c = Some (Store SZ8 2 25 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb10 : bv 32 := 0x00058413.
Lemma F_5fb10 : fetch_word AsanUbsan.M.loaded_segments (0x5fb58 : word) = Some W_5fb10.
Proof. vm_refl. Qed.
Lemma D_5fb10 : decode_any W_5fb10 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb14 : bv 32 := 0xfff68c13.
Lemma F_5fb14 : fetch_word AsanUbsan.M.loaded_segments (0x5fb5c : word) = Some W_5fb14.
Proof. vm_refl. Qed.
Lemma D_5fb14 : decode_any W_5fb14 = Some (OpImm ALU_ADD 24 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb18 : bv 32 := 0x0186f5b3.
Lemma F_5fb18 : fetch_word AsanUbsan.M.loaded_segments (0x5fb60 : word) = Some W_5fb18.
Proof. vm_refl. Qed.
Lemma D_5fb18 : decode_any W_5fb18 = Some (Op ALU_AND 11 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb1c : bv 32 := 0x2c059a63.
Lemma F_5fb1c : fetch_word AsanUbsan.M.loaded_segments (0x5fb64 : word) = Some W_5fb1c.
Proof. vm_refl. Qed.
Lemma D_5fb1c : decode_any W_5fb1c = Some (Branch BC_NE 11 0 724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb20 : bv 32 := 0x00050493.
Lemma F_5fb20 : fetch_word AsanUbsan.M.loaded_segments (0x5fb68 : word) = Some W_5fb20.
Proof. vm_refl. Qed.
Lemma D_5fb20 : decode_any W_5fb20 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb24 : bv 32 := 0x00053503.
Lemma F_5fb24 : fetch_word AsanUbsan.M.loaded_segments (0x5fb6c : word) = Some W_5fb24.
Proof. vm_refl. Qed.
Lemma D_5fb24 : decode_any W_5fb24 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb28 : bv 32 := 0xfff50593.
Lemma F_5fb28 : fetch_word AsanUbsan.M.loaded_segments (0x5fb70 : word) = Some W_5fb28.
Proof. vm_refl. Qed.
Lemma D_5fb28 : decode_any W_5fb28 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb2c : bv 32 := 0x00b575b3.
Lemma F_5fb2c : fetch_word AsanUbsan.M.loaded_segments (0x5fb74 : word) = Some W_5fb2c.
Proof. vm_refl. Qed.
Lemma D_5fb2c : decode_any W_5fb2c = Some (Op ALU_AND 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb30 : bv 32 := 0x2e059063.
Lemma F_5fb30 : fetch_word AsanUbsan.M.loaded_segments (0x5fb78 : word) = Some W_5fb30.
Proof. vm_refl. Qed.
Lemma D_5fb30 : decode_any W_5fb30 = Some (Branch BC_NE 11 0 736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb34 : bv 32 := 0x00060993.
Lemma F_5fb34 : fetch_word AsanUbsan.M.loaded_segments (0x5fb7c : word) = Some W_5fb34.
Proof. vm_refl. Qed.
Lemma D_5fb34 : decode_any W_5fb34 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb38 : bv 32 := 0x00a605b3.
Lemma F_5fb38 : fetch_word AsanUbsan.M.loaded_segments (0x5fb80 : word) = Some W_5fb38.
Proof. vm_refl. Qed.
Lemma D_5fb38 : decode_any W_5fb38 = Some (Op ALU_ADD 11 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb3c : bv 32 := 0x40a00633.
Lemma F_5fb3c : fetch_word AsanUbsan.M.loaded_segments (0x5fb84 : word) = Some W_5fb3c.
Proof. vm_refl. Qed.
Lemma D_5fb3c : decode_any W_5fb3c = Some (Op ALU_SUB 12 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb40 : bv 32 := 0xfff58593.
Lemma F_5fb40 : fetch_word AsanUbsan.M.loaded_segments (0x5fb88 : word) = Some W_5fb40.
Proof. vm_refl. Qed.
Lemma D_5fb40 : decode_any W_5fb40 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb44 : bv 32 := 0x00c5f5b3.
Lemma F_5fb44 : fetch_word AsanUbsan.M.loaded_segments (0x5fb8c : word) = Some W_5fb44.
Proof. vm_refl. Qed.
Lemma D_5fb44 : decode_any W_5fb44 = Some (Op ALU_AND 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb48 : bv 32 := 0x00d53633.
Lemma F_5fb48 : fetch_word AsanUbsan.M.loaded_segments (0x5fb90 : word) = Some W_5fb48.
Proof. vm_refl. Qed.
Lemma D_5fb48 : decode_any W_5fb48 = Some (Op ALU_SLTU 12 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb4c : bv 32 := 0x40c00633.
Lemma F_5fb4c : fetch_word AsanUbsan.M.loaded_segments (0x5fb94 : word) = Some W_5fb4c.
Proof. vm_refl. Qed.
Lemma D_5fb4c : decode_any W_5fb4c = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb50 : bv 32 := 0x00a58533.
Lemma F_5fb50 : fetch_word AsanUbsan.M.loaded_segments (0x5fb98 : word) = Some W_5fb50.
Proof. vm_refl. Qed.
Lemma D_5fb50 : decode_any W_5fb50 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb54 : bv 32 := 0x00d67633.
Lemma F_5fb54 : fetch_word AsanUbsan.M.loaded_segments (0x5fb9c : word) = Some W_5fb54.
Proof. vm_refl. Qed.
Lemma D_5fb54 : decode_any W_5fb54 = Some (Op ALU_AND 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb58 : bv 32 := 0x00c50933.
Lemma F_5fb58 : fetch_word AsanUbsan.M.loaded_segments (0x5fba0 : word) = Some W_5fb58.
Proof. vm_refl. Qed.
Lemma D_5fb58 : decode_any W_5fb58 = Some (Op ALU_ADD 18 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb5c : bv 32 := 0x03397463.
Lemma F_5fb5c : fetch_word AsanUbsan.M.loaded_segments (0x5fba4 : word) = Some W_5fb5c.
Proof. vm_refl. Qed.
Lemma D_5fb5c : decode_any W_5fb5c = Some (Branch BC_GEU 18 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb84 : bv 32 := 0x00068a93.
Lemma F_5fb84 : fetch_word AsanUbsan.M.loaded_segments (0x5fbcc : word) = Some W_5fb84.
Proof. vm_refl. Qed.
Lemma D_5fb84 : decode_any W_5fb84 = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb88 : bv 32 := 0x00105517.
Lemma F_5fb88 : fetch_word AsanUbsan.M.loaded_segments (0x5fbd0 : word) = Some W_5fb88.
Proof. vm_refl. Qed.
Lemma D_5fb88 : decode_any W_5fb88 = Some (Auipc 10 261, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb8c : bv 32 := 0x93053503.
Lemma F_5fb8c : fetch_word AsanUbsan.M.loaded_segments (0x5fbd4 : word) = Some W_5fb8c.
Proof. vm_refl. Qed.
Lemma D_5fb8c : decode_any W_5fb8c = Some (Load SZ8 true 10 10 2352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb90 : bv 32 := 0x00053583.
Lemma F_5fb90 : fetch_word AsanUbsan.M.loaded_segments (0x5fbd8 : word) = Some W_5fb90.
Proof. vm_refl. Qed.
Lemma D_5fb90 : decode_any W_5fb90 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb94 : bv 32 := 0x00090513.
Lemma F_5fb94 : fetch_word AsanUbsan.M.loaded_segments (0x5fbdc : word) = Some W_5fb94.
Proof. vm_refl. Qed.
Lemma D_5fb94 : decode_any W_5fb94 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb98 : bv 32 := 0x7e4360ef.
Lemma F_5fb98 : fetch_word AsanUbsan.M.loaded_segments (0x5fbe0 : word) = Some W_5fb98.
Proof. vm_refl. Qed.
Lemma D_5fb98 : decode_any W_5fb98 = Some (Jal 1 223204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb9c : bv 32 := 0x22050063.
Lemma F_5fb9c : fetch_word AsanUbsan.M.loaded_segments (0x5fbe4 : word) = Some W_5fb9c.
Proof. vm_refl. Qed.
Lemma D_5fb9c : decode_any W_5fb9c = Some (Branch BC_EQ 10 0 544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fba0 : bv 32 := 0x00050a13.
Lemma F_5fba0 : fetch_word AsanUbsan.M.loaded_segments (0x5fbe8 : word) = Some W_5fba0.
Proof. vm_refl. Qed.
Lemma D_5fba0 : decode_any W_5fba0 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fba4 : bv 32 := 0x0004b503.
Lemma F_5fba4 : fetch_word AsanUbsan.M.loaded_segments (0x5fbec : word) = Some W_5fba4.
Proof. vm_refl. Qed.
Lemma D_5fba4 : decode_any W_5fba4 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fba8 : bv 32 := 0xfff50593.
Lemma F_5fba8 : fetch_word AsanUbsan.M.loaded_segments (0x5fbf0 : word) = Some W_5fba8.
Proof. vm_refl. Qed.
Lemma D_5fba8 : decode_any W_5fba8 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbac : bv 32 := 0x0145f5b3.
Lemma F_5fbac : fetch_word AsanUbsan.M.loaded_segments (0x5fbf4 : word) = Some W_5fbac.
Proof. vm_refl. Qed.
Lemma D_5fbac : decode_any W_5fbac = Some (Op ALU_AND 11 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbb0 : bv 32 := 0x26059863.
Lemma F_5fbb0 : fetch_word AsanUbsan.M.loaded_segments (0x5fbf8 : word) = Some W_5fbb0.
Proof. vm_refl. Qed.
Lemma D_5fbb0 : decode_any W_5fbb0 = Some (Branch BC_NE 11 0 624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbb4 : bv 32 := 0x01490b33.
Lemma F_5fbb4 : fetch_word AsanUbsan.M.loaded_segments (0x5fbfc : word) = Some W_5fbb4.
Proof. vm_refl. Qed.
Lemma D_5fbb4 : decode_any W_5fbb4 = Some (Op ALU_ADD 22 18 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbb8 : bv 32 := 0x01450533.
Lemma F_5fbb8 : fetch_word AsanUbsan.M.loaded_segments (0x5fc00 : word) = Some W_5fbb8.
Proof. vm_refl. Qed.
Lemma D_5fbb8 : decode_any W_5fbb8 = Some (Op ALU_ADD 10 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbbc : bv 32 := 0x018575b3.
Lemma F_5fbbc : fetch_word AsanUbsan.M.loaded_segments (0x5fc04 : word) = Some W_5fbbc.
Proof. vm_refl. Qed.
Lemma D_5fbbc : decode_any W_5fbbc = Some (Op ALU_AND 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbc0 : bv 32 := 0x0015b613.
Lemma F_5fbc0 : fetch_word AsanUbsan.M.loaded_segments (0x5fc08 : word) = Some W_5fbc0.
Proof. vm_refl. Qed.
Lemma D_5fbc0 : decode_any W_5fbc0 = Some (OpImm ALU_SLTU 12 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbc4 : bv 32 := 0x40ba85b3.
Lemma F_5fbc4 : fetch_word AsanUbsan.M.loaded_segments (0x5fc0c : word) = Some W_5fbc4.
Proof. vm_refl. Qed.
Lemma D_5fbc4 : decode_any W_5fbc4 = Some (Op ALU_SUB 11 21 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbc8 : bv 32 := 0xfff60613.
Lemma F_5fbc8 : fetch_word AsanUbsan.M.loaded_segments (0x5fc10 : word) = Some W_5fbc8.
Proof. vm_refl. Qed.
Lemma D_5fbc8 : decode_any W_5fbc8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbcc : bv 32 := 0x00b675b3.
Lemma F_5fbcc : fetch_word AsanUbsan.M.loaded_segments (0x5fc14 : word) = Some W_5fbcc.
Proof. vm_refl. Qed.
Lemma D_5fbcc : decode_any W_5fbcc = Some (Op ALU_AND 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbd0 : bv 32 := 0x00a58cb3.
Lemma F_5fbd0 : fetch_word AsanUbsan.M.loaded_segments (0x5fc18 : word) = Some W_5fbd0.
Proof. vm_refl. Qed.
Lemma D_5fbd0 : decode_any W_5fbd0 = Some (Op ALU_ADD 25 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbd4 : bv 32 := 0x013c8ab3.
Lemma F_5fbd4 : fetch_word AsanUbsan.M.loaded_segments (0x5fc1c : word) = Some W_5fbd4.
Proof. vm_refl. Qed.
Lemma D_5fbd4 : decode_any W_5fbd4 = Some (Op ALU_ADD 21 25 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbd8 : bv 32 := 0x007c8513.
Lemma F_5fbd8 : fetch_word AsanUbsan.M.loaded_segments (0x5fc20 : word) = Some W_5fbd8.
Proof. vm_refl. Qed.
Lemma D_5fbd8 : decode_any W_5fbd8 = Some (OpImm ALU_ADD 10 25 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbdc : bv 32 := 0xff8afb93.
Lemma F_5fbdc : fetch_word AsanUbsan.M.loaded_segments (0x5fc24 : word) = Some W_5fbdc.
Proof. vm_refl. Qed.
Lemma D_5fbdc : decode_any W_5fbdc = Some (OpImm ALU_AND 23 21 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbe0 : bv 32 := 0xff857513.
Lemma F_5fbe0 : fetch_word AsanUbsan.M.loaded_segments (0x5fc28 : word) = Some W_5fbe0.
Proof. vm_refl. Qed.
Lemma D_5fbe0 : decode_any W_5fbe0 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbe4 : bv 32 := 0x414505b3.
Lemma F_5fbe4 : fetch_word AsanUbsan.M.loaded_segments (0x5fc2c : word) = Some W_5fbe4.
Proof. vm_refl. Qed.
Lemma D_5fbe4 : decode_any W_5fbe4 = Some (Op ALU_SUB 11 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbe8 : bv 32 := 0x0fa00613.
Lemma F_5fbe8 : fetch_word AsanUbsan.M.loaded_segments (0x5fc30 : word) = Some W_5fbe8.
Proof. vm_refl. Qed.
Lemma D_5fbe8 : decode_any W_5fbe8 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbec : bv 32 := 0x000a0513.
Lemma F_5fbec : fetch_word AsanUbsan.M.loaded_segments (0x5fc34 : word) = Some W_5fbec.
Proof. vm_refl. Qed.
Lemma D_5fbec : decode_any W_5fbec = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbf0 : bv 32 := 0x57d230ef.
Lemma F_5fbf0 : fetch_word AsanUbsan.M.loaded_segments (0x5fc38 : word) = Some W_5fbf0.
Proof. vm_refl. Qed.
Lemma D_5fbf0 : decode_any W_5fbf0 = Some (Jal 1 146812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbf4 : bv 32 := 0x417b05b3.
Lemma F_5fbf4 : fetch_word AsanUbsan.M.loaded_segments (0x5fc3c : word) = Some W_5fbf4.
Proof. vm_refl. Qed.
Lemma D_5fbf4 : decode_any W_5fbf4 = Some (Op ALU_SUB 11 22 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbf8 : bv 32 := 0x0fa00613.
Lemma F_5fbf8 : fetch_word AsanUbsan.M.loaded_segments (0x5fc40 : word) = Some W_5fbf8.
Proof. vm_refl. Qed.
Lemma D_5fbf8 : decode_any W_5fbf8 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbfc : bv 32 := 0x000b8513.
Lemma F_5fbfc : fetch_word AsanUbsan.M.loaded_segments (0x5fc44 : word) = Some W_5fbfc.
Proof. vm_refl. Qed.
Lemma D_5fbfc : decode_any W_5fbfc = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc00 : bv 32 := 0x56d230ef.
Lemma F_5fc00 : fetch_word AsanUbsan.M.loaded_segments (0x5fc48 : word) = Some W_5fc00.
Proof. vm_refl. Qed.
Lemma D_5fc00 : decode_any W_5fc00 = Some (Jal 1 146796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc04 : bv 32 := 0x4e12b0ef.
Lemma F_5fc04 : fetch_word AsanUbsan.M.loaded_segments (0x5fc4c : word) = Some W_5fc04.
Proof. vm_refl. Qed.
Lemma D_5fc04 : decode_any W_5fc04 = Some (Jal 1 179424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc08 : bv 32 := 0x04853603.
Lemma F_5fc08 : fetch_word AsanUbsan.M.loaded_segments (0x5fc50 : word) = Some W_5fc08.
Proof. vm_refl. Qed.
Lemma D_5fc08 : decode_any W_5fc08 = Some (Load SZ8 true 12 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc0c : bv 32 := 0x05053683.
Lemma F_5fc0c : fetch_word AsanUbsan.M.loaded_segments (0x5fc54 : word) = Some W_5fc0c.
Proof. vm_refl. Qed.
Lemma D_5fc0c : decode_any W_5fc0c = Some (Load SZ8 true 13 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc10 : bv 32 := 0x018cf733.
Lemma F_5fc10 : fetch_word AsanUbsan.M.loaded_segments (0x5fc58 : word) = Some W_5fc10.
Proof. vm_refl. Qed.
Lemma D_5fc10 : decode_any W_5fc10 = Some (Op ALU_AND 14 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc14 : bv 32 := 0x00160613.
Lemma F_5fc14 : fetch_word AsanUbsan.M.loaded_segments (0x5fc5c : word) = Some W_5fc14.
Proof. vm_refl. Qed.
Lemma D_5fc14 : decode_any W_5fc14 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc18 : bv 32 := 0x012686b3.
Lemma F_5fc18 : fetch_word AsanUbsan.M.loaded_segments (0x5fc60 : word) = Some W_5fc18.
Proof. vm_refl. Qed.
Lemma D_5fc18 : decode_any W_5fc18 = Some (Op ALU_ADD 13 13 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc1c : bv 32 := 0x04c53423.
Lemma F_5fc1c : fetch_word AsanUbsan.M.loaded_segments (0x5fc64 : word) = Some W_5fc1c.
Proof. vm_refl. Qed.
Lemma D_5fc1c : decode_any W_5fc1c = Some (Store SZ8 10 12 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc20 : bv 32 := 0x04d53823.
Lemma F_5fc20 : fetch_word AsanUbsan.M.loaded_segments (0x5fc68 : word) = Some W_5fc20.
Proof. vm_refl. Qed.
Lemma D_5fc20 : decode_any W_5fc20 = Some (Store SZ8 10 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc24 : bv 32 := 0x20071e63.
Lemma F_5fc24 : fetch_word AsanUbsan.M.loaded_segments (0x5fc6c : word) = Some W_5fc24.
Proof. vm_refl. Qed.
Lemma D_5fc24 : decode_any W_5fc24 = Some (Branch BC_NE 14 0 540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc28 : bv 32 := 0x000c8513.
Lemma F_5fc28 : fetch_word AsanUbsan.M.loaded_segments (0x5fc70 : word) = Some W_5fc28.
Proof. vm_refl. Qed.
Lemma D_5fc28 : decode_any W_5fc28 = Some (OpImm ALU_ADD 10 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc2c : bv 32 := 0x0004b583.
Lemma F_5fc2c : fetch_word AsanUbsan.M.loaded_segments (0x5fc74 : word) = Some W_5fc2c.
Proof. vm_refl. Qed.
Lemma D_5fc2c : decode_any W_5fc2c = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc30 : bv 32 := 0xfff58613.
Lemma F_5fc30 : fetch_word AsanUbsan.M.loaded_segments (0x5fc78 : word) = Some W_5fc30.
Proof. vm_refl. Qed.
Lemma D_5fc30 : decode_any W_5fc30 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc34 : bv 32 := 0x01967633.
Lemma F_5fc34 : fetch_word AsanUbsan.M.loaded_segments (0x5fc7c : word) = Some W_5fc34.
Proof. vm_refl. Qed.
Lemma D_5fc34 : decode_any W_5fc34 = Some (Op ALU_AND 12 12 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc38 : bv 32 := 0x22061463.
Lemma F_5fc38 : fetch_word AsanUbsan.M.loaded_segments (0x5fc80 : word) = Some W_5fc38.
Proof. vm_refl. Qed.
Lemma D_5fc38 : decode_any W_5fc38 = Some (Branch BC_NE 12 0 552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc3c : bv 32 := 0x254ae263.
Lemma F_5fc3c : fetch_word AsanUbsan.M.loaded_segments (0x5fc84 : word) = Some W_5fc3c.
Proof. vm_refl. Qed.
Lemma D_5fc3c : decode_any W_5fc3c = Some (Branch BC_LTU 21 20 580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc40 : bv 32 := 0x275b6063.
Lemma F_5fc40 : fetch_word AsanUbsan.M.loaded_segments (0x5fc88 : word) = Some W_5fc40.
Proof. vm_refl. Qed.
Lemma D_5fc40 : decode_any W_5fc40 = Some (Branch BC_LTU 22 21 608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc44 : bv 32 := 0x40b50ab3.
Lemma F_5fc44 : fetch_word AsanUbsan.M.loaded_segments (0x5fc8c : word) = Some W_5fc44.
Proof. vm_refl. Qed.
Lemma D_5fc44 : decode_any W_5fc44 = Some (Op ALU_SUB 21 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc48 : bv 32 := 0x014ab023.
Lemma F_5fc48 : fetch_word AsanUbsan.M.loaded_segments (0x5fc90 : word) = Some W_5fc48.
Proof. vm_refl. Qed.
Lemma D_5fc48 : decode_any W_5fc48 = Some (Store SZ8 21 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc4c : bv 32 := 0x012ab423.
Lemma F_5fc4c : fetch_word AsanUbsan.M.loaded_segments (0x5fc94 : word) = Some W_5fc4c.
Proof. vm_refl. Qed.
Lemma D_5fc4c : decode_any W_5fc4c = Some (Store SZ8 21 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc50 : bv 32 := 0x013ab823.
Lemma F_5fc50 : fetch_word AsanUbsan.M.loaded_segments (0x5fc98 : word) = Some W_5fc50.
Proof. vm_refl. Qed.
Lemma D_5fc50 : decode_any W_5fc50 = Some (Store SZ8 21 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc54 : bv 32 := 0x26090663.
Lemma F_5fc54 : fetch_word AsanUbsan.M.loaded_segments (0x5fc9c : word) = Some W_5fc54.
Proof. vm_refl. Qed.
Lemma D_5fc54 : decode_any W_5fc54 = Some (Branch BC_EQ 18 0 620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc58 : bv 32 := 0x26848593.
Lemma F_5fc58 : fetch_word AsanUbsan.M.loaded_segments (0x5fca0 : word) = Some W_5fc58.
Proof. vm_refl. Qed.
Lemma D_5fc58 : decode_any W_5fc58 = Some (OpImm ALU_ADD 11 9 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc5c : bv 32 := 0x0ff00613.
Lemma F_5fc5c : fetch_word AsanUbsan.M.loaded_segments (0x5fca4 : word) = Some W_5fc5c.
Proof. vm_refl. Qed.
Lemma D_5fc5c : decode_any W_5fc5c = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc60 : bv 32 := 0xffc5f693.
Lemma F_5fc60 : fetch_word AsanUbsan.M.loaded_segments (0x5fca8 : word) = Some W_5fc60.
Proof. vm_refl. Qed.
Lemma D_5fc60 : decode_any W_5fc60 = Some (OpImm ALU_AND 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc64 : bv 32 := 0x00100713.
Lemma F_5fc64 : fetch_word AsanUbsan.M.loaded_segments (0x5fcac : word) = Some W_5fc64.
Proof. vm_refl. Qed.
Lemma D_5fc64 : decode_any W_5fc64 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc68 : bv 32 := 0x1406a7af.
Lemma F_5fc68 : fetch_word AsanUbsan.M.loaded_segments (0x5fcb0 : word) = Some W_5fc68.
Proof. vm_refl. Qed.
Lemma D_5fc68 : decode_any W_5fc68 = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc6c : bv 32 := 0x00070813.
Lemma F_5fc6c : fetch_word AsanUbsan.M.loaded_segments (0x5fcb4 : word) = Some W_5fc6c.
Proof. vm_refl. Qed.
Lemma D_5fc6c : decode_any W_5fc6c = Some (OpImm ALU_ADD 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc70 : bv 32 := 0x0107c833.
Lemma F_5fc70 : fetch_word AsanUbsan.M.loaded_segments (0x5fcb8 : word) = Some W_5fc70.
Proof. vm_refl. Qed.
Lemma D_5fc70 : decode_any W_5fc70 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc74 : bv 32 := 0x00c87833.
Lemma F_5fc74 : fetch_word AsanUbsan.M.loaded_segments (0x5fcbc : word) = Some W_5fc74.
Proof. vm_refl. Qed.
Lemma D_5fc74 : decode_any W_5fc74 = Some (Op ALU_AND 16 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc78 : bv 32 := 0x0107c833.
Lemma F_5fc78 : fetch_word AsanUbsan.M.loaded_segments (0x5fcc0 : word) = Some W_5fc78.
Proof. vm_refl. Qed.
Lemma D_5fc78 : decode_any W_5fc78 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc7c : bv 32 := 0x1906a82f.
Lemma F_5fc7c : fetch_word AsanUbsan.M.loaded_segments (0x5fcc4 : word) = Some W_5fc7c.
Proof. vm_refl. Qed.
Lemma D_5fc7c : decode_any W_5fc7c = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc80 : bv 32 := 0xfe0814e3.
Lemma F_5fc80 : fetch_word AsanUbsan.M.loaded_segments (0x5fcc8 : word) = Some W_5fc80.
Proof. vm_refl. Qed.
Lemma D_5fc80 : decode_any W_5fc80 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc84 : bv 32 := 0x0ff7f613.
Lemma F_5fc84 : fetch_word AsanUbsan.M.loaded_segments (0x5fccc : word) = Some W_5fc84.
Proof. vm_refl. Qed.
Lemma D_5fc84 : decode_any W_5fc84 = Some (OpImm ALU_AND 12 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc88 : bv 32 := 0x24061c63.
Lemma F_5fc88 : fetch_word AsanUbsan.M.loaded_segments (0x5fcd0 : word) = Some W_5fc88.
Proof. vm_refl. Qed.
Lemma D_5fc88 : decode_any W_5fc88 = Some (Branch BC_NE 12 0 600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc8c : bv 32 := 0x0384b683.
Lemma F_5fc8c : fetch_word AsanUbsan.M.loaded_segments (0x5fcd4 : word) = Some W_5fc8c.
Proof. vm_refl. Qed.
Lemma D_5fc8c : decode_any W_5fc8c = Some (Load SZ8 true 13 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc90 : bv 32 := 0x0146d593.
Lemma F_5fc90 : fetch_word AsanUbsan.M.loaded_segments (0x5fcd8 : word) = Some W_5fc90.
Proof. vm_refl. Qed.
Lemma D_5fc90 : decode_any W_5fc90 = Some (ShiftImm ALU_SRL 11 13 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc94 : bv 32 := 0x26059463.
Lemma F_5fc94 : fetch_word AsanUbsan.M.loaded_segments (0x5fcdc : word) = Some W_5fc94.
Proof. vm_refl. Qed.
Lemma D_5fc94 : decode_any W_5fc94 = Some (Branch BC_NE 11 0 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc98 : bv 32 := 0x00195593.
Lemma F_5fc98 : fetch_word AsanUbsan.M.loaded_segments (0x5fce0 : word) = Some W_5fc98.
Proof. vm_refl. Qed.
Lemma D_5fc98 : decode_any W_5fc98 = Some (ShiftImm ALU_SRL 11 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc9c : bv 32 := 0x55555637.
Lemma F_5fc9c : fetch_word AsanUbsan.M.loaded_segments (0x5fce4 : word) = Some W_5fc9c.
Proof. vm_refl. Qed.
Lemma D_5fc9c : decode_any W_5fc9c = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fca0 : bv 32 := 0x33333737.
Lemma F_5fca0 : fetch_word AsanUbsan.M.loaded_segments (0x5fce8 : word) = Some W_5fca0.
Proof. vm_refl. Qed.
Lemma D_5fca0 : decode_any W_5fca0 = Some (Lui 14 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fca4 : bv 32 := 0x0f0f17b7.
Lemma F_5fca4 : fetch_word AsanUbsan.M.loaded_segments (0x5fcec : word) = Some W_5fca4.
Proof. vm_refl. Qed.
Lemma D_5fca4 : decode_any W_5fca4 = Some (Lui 15 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fca8 : bv 32 := 0x00b965b3.
Lemma F_5fca8 : fetch_word AsanUbsan.M.loaded_segments (0x5fcf0 : word) = Some W_5fca8.
Proof. vm_refl. Qed.
Lemma D_5fca8 : decode_any W_5fca8 = Some (Op ALU_OR 11 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcac : bv 32 := 0x5556061b.
Lemma F_5fcac : fetch_word AsanUbsan.M.loaded_segments (0x5fcf4 : word) = Some W_5fcac.
Proof. vm_refl. Qed.
Lemma D_5fcac : decode_any W_5fcac = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcb0 : bv 32 := 0x3337071b.
Lemma F_5fcb0 : fetch_word AsanUbsan.M.loaded_segments (0x5fcf8 : word) = Some W_5fcb0.
Proof. vm_refl. Qed.
Lemma D_5fcb0 : decode_any W_5fcb0 = Some (OpImm32 14 14 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcb4 : bv 32 := 0xf0f7879b.
Lemma F_5fcb4 : fetch_word AsanUbsan.M.loaded_segments (0x5fcfc : word) = Some W_5fcb4.
Proof. vm_refl. Qed.
Lemma D_5fcb4 : decode_any W_5fcb4 = Some (OpImm32 15 15 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcb8 : bv 32 := 0x0025d813.
Lemma F_5fcb8 : fetch_word AsanUbsan.M.loaded_segments (0x5fd00 : word) = Some W_5fcb8.
Proof. vm_refl. Qed.
Lemma D_5fcb8 : decode_any W_5fcb8 = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcbc : bv 32 := 0x0105e5b3.
Lemma F_5fcbc : fetch_word AsanUbsan.M.loaded_segments (0x5fd04 : word) = Some W_5fcbc.
Proof. vm_refl. Qed.
Lemma D_5fcbc : decode_any W_5fcbc = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcc0 : bv 32 := 0x02061813.
Lemma F_5fcc0 : fetch_word AsanUbsan.M.loaded_segments (0x5fd08 : word) = Some W_5fcc0.
Proof. vm_refl. Qed.
Lemma D_5fcc0 : decode_any W_5fcc0 = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcc4 : bv 32 := 0x01060633.
Lemma F_5fcc4 : fetch_word AsanUbsan.M.loaded_segments (0x5fd0c : word) = Some W_5fcc4.
Proof. vm_refl. Qed.
Lemma D_5fcc4 : decode_any W_5fcc4 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcc8 : bv 32 := 0x02071813.
Lemma F_5fcc8 : fetch_word AsanUbsan.M.loaded_segments (0x5fd10 : word) = Some W_5fcc8.
Proof. vm_refl. Qed.
Lemma D_5fcc8 : decode_any W_5fcc8 = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fccc : bv 32 := 0x01070733.
Lemma F_5fccc : fetch_word AsanUbsan.M.loaded_segments (0x5fd14 : word) = Some W_5fccc.
Proof. vm_refl. Qed.
Lemma D_5fccc : decode_any W_5fccc = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcd0 : bv 32 := 0x02079813.
Lemma F_5fcd0 : fetch_word AsanUbsan.M.loaded_segments (0x5fd18 : word) = Some W_5fcd0.
Proof. vm_refl. Qed.
Lemma D_5fcd0 : decode_any W_5fcd0 = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcd4 : bv 32 := 0x010787b3.
Lemma F_5fcd4 : fetch_word AsanUbsan.M.loaded_segments (0x5fd1c : word) = Some W_5fcd4.
Proof. vm_refl. Qed.
Lemma D_5fcd4 : decode_any W_5fcd4 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcd8 : bv 32 := 0x0045d813.
Lemma F_5fcd8 : fetch_word AsanUbsan.M.loaded_segments (0x5fd20 : word) = Some W_5fcd8.
Proof. vm_refl. Qed.
Lemma D_5fcd8 : decode_any W_5fcd8 = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcdc : bv 32 := 0x0105e5b3.
Lemma F_5fcdc : fetch_word AsanUbsan.M.loaded_segments (0x5fd24 : word) = Some W_5fcdc.
Proof. vm_refl. Qed.
Lemma D_5fcdc : decode_any W_5fcdc = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fce0 : bv 32 := 0x0085d813.
Lemma F_5fce0 : fetch_word AsanUbsan.M.loaded_segments (0x5fd28 : word) = Some W_5fce0.
Proof. vm_refl. Qed.
Lemma D_5fce0 : decode_any W_5fce0 = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fce4 : bv 32 := 0x0105e5b3.
Lemma F_5fce4 : fetch_word AsanUbsan.M.loaded_segments (0x5fd2c : word) = Some W_5fce4.
Proof. vm_refl. Qed.
Lemma D_5fce4 : decode_any W_5fce4 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fce8 : bv 32 := 0x0105d813.
Lemma F_5fce8 : fetch_word AsanUbsan.M.loaded_segments (0x5fd30 : word) = Some W_5fce8.
Proof. vm_refl. Qed.
Lemma D_5fce8 : decode_any W_5fce8 = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcec : bv 32 := 0x0105e5b3.
Lemma F_5fcec : fetch_word AsanUbsan.M.loaded_segments (0x5fd34 : word) = Some W_5fcec.
Proof. vm_refl. Qed.
Lemma D_5fcec : decode_any W_5fcec = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcf0 : bv 32 := 0x0205d813.
Lemma F_5fcf0 : fetch_word AsanUbsan.M.loaded_segments (0x5fd38 : word) = Some W_5fcf0.
Proof. vm_refl. Qed.
Lemma D_5fcf0 : decode_any W_5fcf0 = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcf4 : bv 32 := 0x0105e5b3.
Lemma F_5fcf4 : fetch_word AsanUbsan.M.loaded_segments (0x5fd3c : word) = Some W_5fcf4.
Proof. vm_refl. Qed.
Lemma D_5fcf4 : decode_any W_5fcf4 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcf8 : bv 32 := 0xfff5c593.
Lemma F_5fcf8 : fetch_word AsanUbsan.M.loaded_segments (0x5fd40 : word) = Some W_5fcf8.
Proof. vm_refl. Qed.
Lemma D_5fcf8 : decode_any W_5fcf8 = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcfc : bv 32 := 0x0015d813.
Lemma F_5fcfc : fetch_word AsanUbsan.M.loaded_segments (0x5fd44 : word) = Some W_5fcfc.
Proof. vm_refl. Qed.
Lemma D_5fcfc : decode_any W_5fcfc = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd00 : bv 32 := 0x00c87633.
Lemma F_5fd00 : fetch_word AsanUbsan.M.loaded_segments (0x5fd48 : word) = Some W_5fd00.
Proof. vm_refl. Qed.
Lemma D_5fd00 : decode_any W_5fd00 = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd04 : bv 32 := 0x01010837.
Lemma F_5fd04 : fetch_word AsanUbsan.M.loaded_segments (0x5fd4c : word) = Some W_5fd04.
Proof. vm_refl. Qed.
Lemma D_5fd04 : decode_any W_5fd04 = Some (Lui 16 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd08 : bv 32 := 0x40c585b3.
Lemma F_5fd08 : fetch_word AsanUbsan.M.loaded_segments (0x5fd50 : word) = Some W_5fd08.
Proof. vm_refl. Qed.
Lemma D_5fd08 : decode_any W_5fd08 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd0c : bv 32 := 0x0025d613.
Lemma F_5fd0c : fetch_word AsanUbsan.M.loaded_segments (0x5fd54 : word) = Some W_5fd0c.
Proof. vm_refl. Qed.
Lemma D_5fd0c : decode_any W_5fd0c = Some (ShiftImm ALU_SRL 12 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd10 : bv 32 := 0x00e5f5b3.
Lemma F_5fd10 : fetch_word AsanUbsan.M.loaded_segments (0x5fd58 : word) = Some W_5fd10.
Proof. vm_refl. Qed.
Lemma D_5fd10 : decode_any W_5fd10 = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd14 : bv 32 := 0x00e67633.
Lemma F_5fd14 : fetch_word AsanUbsan.M.loaded_segments (0x5fd5c : word) = Some W_5fd14.
Proof. vm_refl. Qed.
Lemma D_5fd14 : decode_any W_5fd14 = Some (Op ALU_AND 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd18 : bv 32 := 0x0304b703.
Lemma F_5fd18 : fetch_word AsanUbsan.M.loaded_segments (0x5fd60 : word) = Some W_5fd18.
Proof. vm_refl. Qed.
Lemma D_5fd18 : decode_any W_5fd18 = Some (Load SZ8 true 14 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd1c : bv 32 := 0x1018081b.
Lemma F_5fd1c : fetch_word AsanUbsan.M.loaded_segments (0x5fd64 : word) = Some W_5fd1c.
Proof. vm_refl. Qed.
Lemma D_5fd1c : decode_any W_5fd1c = Some (OpImm32 16 16 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd20 : bv 32 := 0x00c585b3.
Lemma F_5fd20 : fetch_word AsanUbsan.M.loaded_segments (0x5fd68 : word) = Some W_5fd20.
Proof. vm_refl. Qed.
Lemma D_5fd20 : decode_any W_5fd20 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd24 : bv 32 := 0x0045d613.
Lemma F_5fd24 : fetch_word AsanUbsan.M.loaded_segments (0x5fd6c : word) = Some W_5fd24.
Proof. vm_refl. Qed.
Lemma D_5fd24 : decode_any W_5fd24 = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd28 : bv 32 := 0x00c585b3.
Lemma F_5fd28 : fetch_word AsanUbsan.M.loaded_segments (0x5fd70 : word) = Some W_5fd28.
Proof. vm_refl. Qed.
Lemma D_5fd28 : decode_any W_5fd28 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd2c : bv 32 := 0x02081613.
Lemma F_5fd2c : fetch_word AsanUbsan.M.loaded_segments (0x5fd74 : word) = Some W_5fd2c.
Proof. vm_refl. Qed.
Lemma D_5fd2c : decode_any W_5fd2c = Some (ShiftImm ALU_SLL 12 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd30 : bv 32 := 0x00f5f5b3.
Lemma F_5fd30 : fetch_word AsanUbsan.M.loaded_segments (0x5fd78 : word) = Some W_5fd30.
Proof. vm_refl. Qed.
Lemma D_5fd30 : decode_any W_5fd30 = Some (Op ALU_AND 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd34 : bv 32 := 0x00c80633.
Lemma F_5fd34 : fetch_word AsanUbsan.M.loaded_segments (0x5fd7c : word) = Some W_5fd34.
Proof. vm_refl. Qed.
Lemma D_5fd34 : decode_any W_5fd34 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd38 : bv 32 := 0x02c585b3.
Lemma F_5fd38 : fetch_word AsanUbsan.M.loaded_segments (0x5fd80 : word) = Some W_5fd38.
Proof. vm_refl. Qed.
Lemma D_5fd38 : decode_any W_5fd38 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd3c : bv 32 := 0x0385d993.
Lemma F_5fd3c : fetch_word AsanUbsan.M.loaded_segments (0x5fd84 : word) = Some W_5fd3c.
Proof. vm_refl. Qed.
Lemma D_5fd3c : decode_any W_5fd3c = Some (ShiftImm ALU_SRL 19 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd40 : bv 32 := 0x1ce68c63.
Lemma F_5fd40 : fetch_word AsanUbsan.M.loaded_segments (0x5fd88 : word) = Some W_5fd40.
Proof. vm_refl. Qed.
Lemma D_5fd40 : decode_any W_5fd40 = Some (Branch BC_EQ 13 14 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd44 : bv 32 := 0x0084b603.
Lemma F_5fd44 : fetch_word AsanUbsan.M.loaded_segments (0x5fd8c : word) = Some W_5fd44.
Proof. vm_refl. Qed.
Lemma D_5fd44 : decode_any W_5fd44 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd48 : bv 32 := 0x03f9c593.
Lemma F_5fd48 : fetch_word AsanUbsan.M.loaded_segments (0x5fd90 : word) = Some W_5fd48.
Proof. vm_refl. Qed.
Lemma D_5fd48 : decode_any W_5fd48 = Some (OpImm ALU_XOR 11 19 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd4c : bv 32 := 0x00dabc23.
Lemma F_5fd4c : fetch_word AsanUbsan.M.loaded_segments (0x5fd94 : word) = Some W_5fd4c.
Proof. vm_refl. Qed.
Lemma D_5fd4c : decode_any W_5fd4c = Some (Store SZ8 21 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd50 : bv 32 := 0x00369713.
Lemma F_5fd50 : fetch_word AsanUbsan.M.loaded_segments (0x5fd98 : word) = Some W_5fd50.
Proof. vm_refl. Qed.
Lemma D_5fd50 : decode_any W_5fd50 = Some (ShiftImm ALU_SLL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd54 : bv 32 := 0x00e60633.
Lemma F_5fd54 : fetch_word AsanUbsan.M.loaded_segments (0x5fd9c : word) = Some W_5fd54.
Proof. vm_refl. Qed.
Lemma D_5fd54 : decode_any W_5fd54 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd58 : bv 32 := 0x01563023.
Lemma F_5fd58 : fetch_word AsanUbsan.M.loaded_segments (0x5fda0 : word) = Some W_5fd58.
Proof. vm_refl. Qed.
Lemma D_5fd58 : decode_any W_5fd58 = Some (Store SZ8 12 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd5c : bv 32 := 0x0484b703.
Lemma F_5fd5c : fetch_word AsanUbsan.M.loaded_segments (0x5fda4 : word) = Some W_5fd5c.
Proof. vm_refl. Qed.
Lemma D_5fd5c : decode_any W_5fd5c = Some (Load SZ8 true 14 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd60 : bv 32 := 0x0584b783.
Lemma F_5fd60 : fetch_word AsanUbsan.M.loaded_segments (0x5fda8 : word) = Some W_5fd60.
Proof. vm_refl. Qed.
Lemma D_5fd60 : decode_any W_5fd60 = Some (Load SZ8 true 15 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd64 : bv 32 := 0x00168813.
Lemma F_5fd64 : fetch_word AsanUbsan.M.loaded_segments (0x5fdac : word) = Some W_5fd64.
Proof. vm_refl. Qed.
Lemma D_5fd64 : decode_any W_5fd64 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd68 : bv 32 := 0x0604b603.
Lemma F_5fd68 : fetch_word AsanUbsan.M.loaded_segments (0x5fdb0 : word) = Some W_5fd68.
Proof. vm_refl. Qed.
Lemma D_5fd68 : decode_any W_5fd68 = Some (Load SZ8 true 12 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd6c : bv 32 := 0x00170713.
Lemma F_5fd6c : fetch_word AsanUbsan.M.loaded_segments (0x5fdb4 : word) = Some W_5fd6c.
Proof. vm_refl. Qed.
Lemma D_5fd6c : decode_any W_5fd6c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd70 : bv 32 := 0x012786b3.
Lemma F_5fd70 : fetch_word AsanUbsan.M.loaded_segments (0x5fdb8 : word) = Some W_5fd70.
Proof. vm_refl. Qed.
Lemma D_5fd70 : decode_any W_5fd70 = Some (Op ALU_ADD 13 15 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd74 : bv 32 := 0x0304bc23.
Lemma F_5fd74 : fetch_word AsanUbsan.M.loaded_segments (0x5fdbc : word) = Some W_5fd74.
Proof. vm_refl. Qed.
Lemma D_5fd74 : decode_any W_5fd74 = Some (Store SZ8 9 16 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd78 : bv 32 := 0x04048023.
Lemma F_5fd78 : fetch_word AsanUbsan.M.loaded_segments (0x5fdc0 : word) = Some W_5fd78.
Proof. vm_refl. Qed.
Lemma D_5fd78 : decode_any W_5fd78 = Some (Store SZ1 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd7c : bv 32 := 0x04e4b423.
Lemma F_5fd7c : fetch_word AsanUbsan.M.loaded_segments (0x5fdc4 : word) = Some W_5fd7c.
Proof. vm_refl. Qed.
Lemma D_5fd7c : decode_any W_5fd7c = Some (Store SZ8 9 14 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd80 : bv 32 := 0x04d4bc23.
Lemma F_5fd80 : fetch_word AsanUbsan.M.loaded_segments (0x5fdc8 : word) = Some W_5fd80.
Proof. vm_refl. Qed.
Lemma D_5fd80 : decode_any W_5fd80 = Some (Store SZ8 9 13 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd84 : bv 32 := 0x00c6e463.
Lemma F_5fd84 : fetch_word AsanUbsan.M.loaded_segments (0x5fdcc : word) = Some W_5fd84.
Proof. vm_refl. Qed.
Lemma D_5fd84 : decode_any W_5fd84 = Some (Branch BC_LTU 13 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd88 : bv 32 := 0x00068613.
Lemma F_5fd88 : fetch_word AsanUbsan.M.loaded_segments (0x5fdd0 : word) = Some W_5fd88.
Proof. vm_refl. Qed.
Lemma D_5fd88 : decode_any W_5fd88 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd8c : bv 32 := 0x00359593.
Lemma F_5fd8c : fetch_word AsanUbsan.M.loaded_segments (0x5fdd4 : word) = Some W_5fd8c.
Proof. vm_refl. Qed.
Lemma D_5fd8c : decode_any W_5fd8c = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd90 : bv 32 := 0x00b485b3.
Lemma F_5fd90 : fetch_word AsanUbsan.M.loaded_segments (0x5fdd8 : word) = Some W_5fd90.
Proof. vm_refl. Qed.
Lemma D_5fd90 : decode_any W_5fd90 = Some (Op ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd94 : bv 32 := 0x0685b683.
Lemma F_5fd94 : fetch_word AsanUbsan.M.loaded_segments (0x5fddc : word) = Some W_5fd94.
Proof. vm_refl. Qed.
Lemma D_5fd94 : decode_any W_5fd94 = Some (Load SZ8 true 13 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd98 : bv 32 := 0x00168693.
Lemma F_5fd98 : fetch_word AsanUbsan.M.loaded_segments (0x5fde0 : word) = Some W_5fd98.
Proof. vm_refl. Qed.
Lemma D_5fd98 : decode_any W_5fd98 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fd9c : bv 32 := 0x06c4b023.
Lemma F_5fd9c : fetch_word AsanUbsan.M.loaded_segments (0x5fde4 : word) = Some W_5fd9c.
Proof. vm_refl. Qed.
Lemma D_5fd9c : decode_any W_5fd9c = Some (Store SZ8 9 12 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fda0 : bv 32 := 0x06d5b423.
Lemma F_5fda0 : fetch_word AsanUbsan.M.loaded_segments (0x5fde8 : word) = Some W_5fda0.
Proof. vm_refl. Qed.
Lemma D_5fda0 : decode_any W_5fda0 = Some (Store SZ8 11 13 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fda4 : bv 32 := 0x01040593.
Lemma F_5fda4 : fetch_word AsanUbsan.M.loaded_segments (0x5fdec : word) = Some W_5fda4.
Proof. vm_refl. Qed.
Lemma D_5fda4 : decode_any W_5fda4 = Some (OpImm ALU_ADD 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fda8 : bv 32 := 0x0125b02f.
Lemma F_5fda8 : fetch_word AsanUbsan.M.loaded_segments (0x5fdf0 : word) = Some W_5fda8.
Proof. vm_refl. Qed.
Lemma D_5fda8 : decode_any W_5fda8 = Some (Amo AMO_ADD AD false false 0 11 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdac : bv 32 := 0x01840413.
Lemma F_5fdac : fetch_word AsanUbsan.M.loaded_segments (0x5fdf4 : word) = Some W_5fdac.
Proof. vm_refl. Qed.
Lemma D_5fdac : decode_any W_5fdac = Some (OpImm ALU_ADD 8 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdb0 : bv 32 := 0x0124302f.
Lemma F_5fdb0 : fetch_word AsanUbsan.M.loaded_segments (0x5fdf8 : word) = Some W_5fdb0.
Proof. vm_refl. Qed.
Lemma D_5fdb0 : decode_any W_5fdb0 = Some (Amo AMO_ADD AD false false 0 8 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdb4 : bv 32 := 0x0310000f.
Lemma F_5fdb4 : fetch_word AsanUbsan.M.loaded_segments (0x5fdfc : word) = Some W_5fdb4.
Proof. vm_refl. Qed.
Lemma D_5fdb4 : decode_any W_5fdb4 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdb8 : bv 32 := 0x26048423.
Lemma F_5fdb8 : fetch_word AsanUbsan.M.loaded_segments (0x5fe00 : word) = Some W_5fdb8.
Proof. vm_refl. Qed.
Lemma D_5fdb8 : decode_any W_5fdb8 = Some (Store SZ1 9 0 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdbc : bv 32 := 0x05813083.
Lemma F_5fdbc : fetch_word AsanUbsan.M.loaded_segments (0x5fe04 : word) = Some W_5fdbc.
Proof. vm_refl. Qed.
Lemma D_5fdbc : decode_any W_5fdbc = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdc0 : bv 32 := 0x05013403.
Lemma F_5fdc0 : fetch_word AsanUbsan.M.loaded_segments (0x5fe08 : word) = Some W_5fdc0.
Proof. vm_refl. Qed.
Lemma D_5fdc0 : decode_any W_5fdc0 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdc4 : bv 32 := 0x04813483.
Lemma F_5fdc4 : fetch_word AsanUbsan.M.loaded_segments (0x5fe0c : word) = Some W_5fdc4.
Proof. vm_refl. Qed.
Lemma D_5fdc4 : decode_any W_5fdc4 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdc8 : bv 32 := 0x04013903.
Lemma F_5fdc8 : fetch_word AsanUbsan.M.loaded_segments (0x5fe10 : word) = Some W_5fdc8.
Proof. vm_refl. Qed.
Lemma D_5fdc8 : decode_any W_5fdc8 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdcc : bv 32 := 0x03813983.
Lemma F_5fdcc : fetch_word AsanUbsan.M.loaded_segments (0x5fe14 : word) = Some W_5fdcc.
Proof. vm_refl. Qed.
Lemma D_5fdcc : decode_any W_5fdcc = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdd0 : bv 32 := 0x03013a03.
Lemma F_5fdd0 : fetch_word AsanUbsan.M.loaded_segments (0x5fe18 : word) = Some W_5fdd0.
Proof. vm_refl. Qed.
Lemma D_5fdd0 : decode_any W_5fdd0 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdd4 : bv 32 := 0x02813a83.
Lemma F_5fdd4 : fetch_word AsanUbsan.M.loaded_segments (0x5fe1c : word) = Some W_5fdd4.
Proof. vm_refl. Qed.
Lemma D_5fdd4 : decode_any W_5fdd4 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdd8 : bv 32 := 0x02013b03.
Lemma F_5fdd8 : fetch_word AsanUbsan.M.loaded_segments (0x5fe20 : word) = Some W_5fdd8.
Proof. vm_refl. Qed.
Lemma D_5fdd8 : decode_any W_5fdd8 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fddc : bv 32 := 0x01813b83.
Lemma F_5fddc : fetch_word AsanUbsan.M.loaded_segments (0x5fe24 : word) = Some W_5fddc.
Proof. vm_refl. Qed.
Lemma D_5fddc : decode_any W_5fddc = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fde0 : bv 32 := 0x01013c03.
Lemma F_5fde0 : fetch_word AsanUbsan.M.loaded_segments (0x5fe28 : word) = Some W_5fde0.
Proof. vm_refl. Qed.
Lemma D_5fde0 : decode_any W_5fde0 = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fde4 : bv 32 := 0x00813c83.
Lemma F_5fde4 : fetch_word AsanUbsan.M.loaded_segments (0x5fe2c : word) = Some W_5fde4.
Proof. vm_refl. Qed.
Lemma D_5fde4 : decode_any W_5fde4 = Some (Load SZ8 true 25 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fde8 : bv 32 := 0x06010113.
Lemma F_5fde8 : fetch_word AsanUbsan.M.loaded_segments (0x5fe30 : word) = Some W_5fde8.
Proof. vm_refl. Qed.
Lemma D_5fde8 : decode_any W_5fde8 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdec : bv 32 := 0x00008067.
Lemma F_5fdec : fetch_word AsanUbsan.M.loaded_segments (0x5fe34 : word) = Some W_5fdec.
Proof. vm_refl. Qed.
Lemma D_5fdec : decode_any W_5fdec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff18 : bv 32 := 0x0104b583.
Lemma F_5ff18 : fetch_word AsanUbsan.M.loaded_segments (0x5ff60 : word) = Some W_5ff18.
Proof. vm_refl. Qed.
Lemma D_5ff18 : decode_any W_5ff18 = Some (Load SZ8 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff1c : bv 32 := 0x01048713.
Lemma F_5ff1c : fetch_word AsanUbsan.M.loaded_segments (0x5ff64 : word) = Some W_5ff1c.
Proof. vm_refl. Qed.
Lemma D_5ff1c : decode_any W_5ff1c = Some (OpImm ALU_ADD 14 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff20 : bv 32 := 0x00369693.
Lemma F_5ff20 : fetch_word AsanUbsan.M.loaded_segments (0x5ff68 : word) = Some W_5ff20.
Proof. vm_refl. Qed.
Lemma D_5ff20 : decode_any W_5ff20 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff24 : bv 32 := 0x00b685b3.
Lemma F_5ff24 : fetch_word AsanUbsan.M.loaded_segments (0x5ff6c : word) = Some W_5ff24.
Proof. vm_refl. Qed.
Lemma D_5ff24 : decode_any W_5ff24 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff28 : bv 32 := 0x00020637.
Lemma F_5ff28 : fetch_word AsanUbsan.M.loaded_segments (0x5ff70 : word) = Some W_5ff28.
Proof. vm_refl. Qed.
Lemma D_5ff28 : decode_any W_5ff28 = Some (Lui 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff2c : bv 32 := 0x00050a13.
Lemma F_5ff2c : fetch_word AsanUbsan.M.loaded_segments (0x5ff74 : word) = Some W_5ff2c.
Proof. vm_refl. Qed.
Lemma D_5ff2c : decode_any W_5ff2c = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff30 : bv 32 := 0x00070513.
Lemma F_5ff30 : fetch_word AsanUbsan.M.loaded_segments (0x5ff78 : word) = Some W_5ff30.
Proof. vm_refl. Qed.
Lemma D_5ff30 : decode_any W_5ff30 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff34 : bv 32 := 0x00000693.
Lemma F_5ff34 : fetch_word AsanUbsan.M.loaded_segments (0x5ff7c : word) = Some W_5ff34.
Proof. vm_refl. Qed.
Lemma D_5ff34 : decode_any W_5ff34 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff38 : bv 32 := 0x4153e0ef.
Lemma F_5ff38 : fetch_word AsanUbsan.M.loaded_segments (0x5ff80 : word) = Some W_5ff38.
Proof. vm_refl. Qed.
Lemma D_5ff38 : decode_any W_5ff38 = Some (Jal 1 257044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff3c : bv 32 := 0x000a0513.
Lemma F_5ff3c : fetch_word AsanUbsan.M.loaded_segments (0x5ff84 : word) = Some W_5ff3c.
Proof. vm_refl. Qed.
Lemma D_5ff3c : decode_any W_5ff3c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff40 : bv 32 := 0x0304b583.
Lemma F_5ff40 : fetch_word AsanUbsan.M.loaded_segments (0x5ff88 : word) = Some W_5ff40.
Proof. vm_refl. Qed.
Lemma D_5ff40 : decode_any W_5ff40 = Some (Load SZ8 true 11 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff44 : bv 32 := 0x0384b683.
Lemma F_5ff44 : fetch_word AsanUbsan.M.loaded_segments (0x5ff8c : word) = Some W_5ff44.
Proof. vm_refl. Qed.
Lemma D_5ff44 : decode_any W_5ff44 = Some (Load SZ8 true 13 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff48 : bv 32 := 0x00004637.
Lemma F_5ff48 : fetch_word AsanUbsan.M.loaded_segments (0x5ff90 : word) = Some W_5ff48.
Proof. vm_refl. Qed.
Lemma D_5ff48 : decode_any W_5ff48 = Some (Lui 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff4c : bv 32 := 0x00c585b3.
Lemma F_5ff4c : fetch_word AsanUbsan.M.loaded_segments (0x5ff94 : word) = Some W_5ff4c.
Proof. vm_refl. Qed.
Lemma D_5ff4c : decode_any W_5ff4c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff50 : bv 32 := 0x02b4b823.
Lemma F_5ff50 : fetch_word AsanUbsan.M.loaded_segments (0x5ff98 : word) = Some W_5ff50.
Proof. vm_refl. Qed.
Lemma D_5ff50 : decode_any W_5ff50 = Some (Store SZ8 9 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff54 : bv 32 := 0xdf1ff06f.
Lemma F_5ff54 : fetch_word AsanUbsan.M.loaded_segments (0x5ff9c : word) = Some W_5ff54.
Proof. vm_refl. Qed.
Lemma D_5ff54 : decode_any W_5ff54 = Some (Jal 0 2096624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff58 : bv 32 := 0xfe010113.
Lemma F_5ff58 : fetch_word AsanUbsan.M.loaded_segments (0x5ffa0 : word) = Some W_5ff58.
Proof. vm_refl. Qed.
Lemma D_5ff58 : decode_any W_5ff58 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff5c : bv 32 := 0x00113c23.
Lemma F_5ff5c : fetch_word AsanUbsan.M.loaded_segments (0x5ffa4 : word) = Some W_5ff5c.
Proof. vm_refl. Qed.
Lemma D_5ff5c : decode_any W_5ff5c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff60 : bv 32 := 0x00813823.
Lemma F_5ff60 : fetch_word AsanUbsan.M.loaded_segments (0x5ffa8 : word) = Some W_5ff60.
Proof. vm_refl. Qed.
Lemma D_5ff60 : decode_any W_5ff60 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff64 : bv 32 := 0x00913423.
Lemma F_5ff64 : fetch_word AsanUbsan.M.loaded_segments (0x5ffac : word) = Some W_5ff64.
Proof. vm_refl. Qed.
Lemma D_5ff64 : decode_any W_5ff64 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff68 : bv 32 := 0x00068713.
Lemma F_5ff68 : fetch_word AsanUbsan.M.loaded_segments (0x5ffb0 : word) = Some W_5ff68.
Proof. vm_refl. Qed.
Lemma D_5ff68 : decode_any W_5ff68 = Some (OpImm ALU_ADD 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff6c : bv 32 := 0x00058413.
Lemma F_5ff6c : fetch_word AsanUbsan.M.loaded_segments (0x5ffb4 : word) = Some W_5ff6c.
Proof. vm_refl. Qed.
Lemma D_5ff6c : decode_any W_5ff6c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff70 : bv 32 := 0x0045a583.
Lemma F_5ff70 : fetch_word AsanUbsan.M.loaded_segments (0x5ffb8 : word) = Some W_5ff70.
Proof. vm_refl. Qed.
Lemma D_5ff70 : decode_any W_5ff70 = Some (Load SZ4 true 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff74 : bv 32 := 0x04058063.
Lemma F_5ff74 : fetch_word AsanUbsan.M.loaded_segments (0x5ffbc : word) = Some W_5ff74.
Proof. vm_refl. Qed.
Lemma D_5ff74 : decode_any W_5ff74 = Some (Branch BC_EQ 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff78 : bv 32 := 0x0015d49b.
Lemma F_5ff78 : fetch_word AsanUbsan.M.loaded_segments (0x5ffc0 : word) = Some W_5ff78.
Proof. vm_refl. Qed.
Lemma D_5ff78 : decode_any W_5ff78 = Some (ShiftImm32 ALU_SRL 9 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff7c : bv 32 := 0x7ff50513.
Lemma F_5ff7c : fetch_word AsanUbsan.M.loaded_segments (0x5ffc4 : word) = Some W_5ff7c.
Proof. vm_refl. Qed.
Lemma D_5ff7c : decode_any W_5ff7c = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff80 : bv 32 := 0x20150593.
Lemma F_5ff80 : fetch_word AsanUbsan.M.loaded_segments (0x5ffc8 : word) = Some W_5ff80.
Proof. vm_refl. Qed.
Lemma D_5ff80 : decode_any W_5ff80 = Some (OpImm ALU_ADD 11 10 513, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff84 : bv 32 := 0x01040693.
Lemma F_5ff84 : fetch_word AsanUbsan.M.loaded_segments (0x5ffcc : word) = Some W_5ff84.
Proof. vm_refl. Qed.
Lemma D_5ff84 : decode_any W_5ff84 = Some (OpImm ALU_ADD 13 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff88 : bv 32 := 0x00060513.
Lemma F_5ff88 : fetch_word AsanUbsan.M.loaded_segments (0x5ffd0 : word) = Some W_5ff88.
Proof. vm_refl. Qed.
Lemma D_5ff88 : decode_any W_5ff88 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff8c : bv 32 := 0x00070613.
Lemma F_5ff8c : fetch_word AsanUbsan.M.loaded_segments (0x5ffd4 : word) = Some W_5ff8c.
Proof. vm_refl. Qed.
Lemma D_5ff8c : decode_any W_5ff8c = Some (OpImm ALU_ADD 12 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff90 : bv 32 := 0x00048713.
Lemma F_5ff90 : fetch_word AsanUbsan.M.loaded_segments (0x5ffd8 : word) = Some W_5ff90.
Proof. vm_refl. Qed.
Lemma D_5ff90 : decode_any W_5ff90 = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff94 : bv 32 := 0x0c4000ef.
Lemma F_5ff94 : fetch_word AsanUbsan.M.loaded_segments (0x5ffdc : word) = Some W_5ff94.
Proof. vm_refl. Qed.
Lemma D_5ff94 : decode_any W_5ff94 = Some (Jal 1 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff98 : bv 32 := 0x00050463.
Lemma F_5ff98 : fetch_word AsanUbsan.M.loaded_segments (0x5ffe0 : word) = Some W_5ff98.
Proof. vm_refl. Qed.
Lemma D_5ff98 : decode_any W_5ff98 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ff9c : bv 32 := 0x00942023.
Lemma F_5ff9c : fetch_word AsanUbsan.M.loaded_segments (0x5ffe4 : word) = Some W_5ff9c.
Proof. vm_refl. Qed.
Lemma D_5ff9c : decode_any W_5ff9c = Some (Store SZ4 8 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffa0 : bv 32 := 0x01813083.
Lemma F_5ffa0 : fetch_word AsanUbsan.M.loaded_segments (0x5ffe8 : word) = Some W_5ffa0.
Proof. vm_refl. Qed.
Lemma D_5ffa0 : decode_any W_5ffa0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffa4 : bv 32 := 0x01013403.
Lemma F_5ffa4 : fetch_word AsanUbsan.M.loaded_segments (0x5ffec : word) = Some W_5ffa4.
Proof. vm_refl. Qed.
Lemma D_5ffa4 : decode_any W_5ffa4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffa8 : bv 32 := 0x00813483.
Lemma F_5ffa8 : fetch_word AsanUbsan.M.loaded_segments (0x5fff0 : word) = Some W_5ffa8.
Proof. vm_refl. Qed.
Lemma D_5ffa8 : decode_any W_5ffa8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffac : bv 32 := 0x02010113.
Lemma F_5ffac : fetch_word AsanUbsan.M.loaded_segments (0x5fff4 : word) = Some W_5ffac.
Proof. vm_refl. Qed.
Lemma D_5ffac : decode_any W_5ffac = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffb0 : bv 32 := 0x00008067.
Lemma F_5ffb0 : fetch_word AsanUbsan.M.loaded_segments (0x5fff8 : word) = Some W_5ffb0.
Proof. vm_refl. Qed.
Lemma D_5ffb0 : decode_any W_5ffb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffb4 : bv 32 := 0x05850593.
Lemma F_5ffb4 : fetch_word AsanUbsan.M.loaded_segments (0x5fffc : word) = Some W_5ffb4.
Proof. vm_refl. Qed.
Lemma D_5ffb4 : decode_any W_5ffb4 = Some (OpImm ALU_ADD 11 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffb8 : bv 32 := 0x02000693.
Lemma F_5ffb8 : fetch_word AsanUbsan.M.loaded_segments (0x60000 : word) = Some W_5ffb8.
Proof. vm_refl. Qed.
Lemma D_5ffb8 : decode_any W_5ffb8 = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffbc : bv 32 := 0xff100793.
Lemma F_5ffbc : fetch_word AsanUbsan.M.loaded_segments (0x60004 : word) = Some W_5ffbc.
Proof. vm_refl. Qed.
Lemma D_5ffbc : decode_any W_5ffbc = Some (OpImm ALU_ADD 15 0 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffc0 : bv 32 := 0x00f00813.
Lemma F_5ffc0 : fetch_word AsanUbsan.M.loaded_segments (0x60008 : word) = Some W_5ffc0.
Proof. vm_refl. Qed.
Lemma D_5ffc0 : decode_any W_5ffc0 = Some (OpImm ALU_ADD 16 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffc4 : bv 32 := 0x40000893.
Lemma F_5ffc4 : fetch_word AsanUbsan.M.loaded_segments (0x6000c : word) = Some W_5ffc4.
Proof. vm_refl. Qed.
Lemma D_5ffc4 : decode_any W_5ffc4 = Some (OpImm ALU_ADD 17 0 1024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffc8 : bv 32 := 0x01000293.
Lemma F_5ffc8 : fetch_word AsanUbsan.M.loaded_segments (0x60010 : word) = Some W_5ffc8.
Proof. vm_refl. Qed.
Lemma D_5ffc8 : decode_any W_5ffc8 = Some (OpImm ALU_ADD 5 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffcc : bv 32 := 0x01100313.
Lemma F_5ffcc : fetch_word AsanUbsan.M.loaded_segments (0x60014 : word) = Some W_5ffcc.
Proof. vm_refl. Qed.
Lemma D_5ffcc : decode_any W_5ffcc = Some (OpImm ALU_ADD 6 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffd0 : bv 32 := 0x20000393.
Lemma F_5ffd0 : fetch_word AsanUbsan.M.loaded_segments (0x60018 : word) = Some W_5ffd0.
Proof. vm_refl. Qed.
Lemma D_5ffd0 : decode_any W_5ffd0 = Some (OpImm ALU_ADD 7 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffd4 : bv 32 := 0x0280006f.
Lemma F_5ffd4 : fetch_word AsanUbsan.M.loaded_segments (0x6001c : word) = Some W_5ffd4.
Proof. vm_refl. Qed.
Lemma D_5ffd4 : decode_any W_5ffd4 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffd8 : bv 32 := 0x001ebf13.
Lemma F_5ffd8 : fetch_word AsanUbsan.M.loaded_segments (0x60020 : word) = Some W_5ffd8.
Proof. vm_refl. Qed.
Lemma D_5ffd8 : decode_any W_5ffd8 = Some (OpImm ALU_SLTU 30 29 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffdc : bv 32 := 0x02068693.
Lemma F_5ffdc : fetch_word AsanUbsan.M.loaded_segments (0x60024 : word) = Some W_5ffdc.
Proof. vm_refl. Qed.
Lemma D_5ffdc : decode_any W_5ffdc = Some (OpImm ALU_ADD 13 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffe0 : bv 32 := 0x00178793.
Lemma F_5ffe0 : fetch_word AsanUbsan.M.loaded_segments (0x60028 : word) = Some W_5ffe0.
Proof. vm_refl. Qed.
Lemma D_5ffe0 : decode_any W_5ffe0 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffe4 : bv 32 := 0x01ee8eb3.
Lemma F_5ffe4 : fetch_word AsanUbsan.M.loaded_segments (0x6002c : word) = Some W_5ffe4.
Proof. vm_refl. Qed.
Lemma D_5ffe4 : decode_any W_5ffe4 = Some (Op ALU_ADD 29 29 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffe8 : bv 32 := 0x001e9e93.
Lemma F_5ffe8 : fetch_word AsanUbsan.M.loaded_segments (0x60030 : word) = Some W_5ffe8.
Proof. vm_refl. Qed.
Lemma D_5ffe8 : decode_any W_5ffe8 = Some (ShiftImm ALU_SLL 29 29 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffec : bv 32 := 0xffd5ae23.
Lemma F_5ffec : fetch_word AsanUbsan.M.loaded_segments (0x60034 : word) = Some W_5ffec.
Proof. vm_refl. Qed.
Lemma D_5ffec : decode_any W_5ffec = Some (Store SZ4 11 29 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fff0 : bv 32 := 0x01c5b023.
Lemma F_5fff0 : fetch_word AsanUbsan.M.loaded_segments (0x60038 : word) = Some W_5fff0.
Proof. vm_refl. Qed.
Lemma D_5fff0 : decode_any W_5fff0 = Some (Store SZ8 11 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fff4 : bv 32 := 0x05058593.
Lemma F_5fff4 : fetch_word AsanUbsan.M.loaded_segments (0x6003c : word) = Some W_5fff4.
Proof. vm_refl. Qed.
Lemma D_5fff4 : decode_any W_5fff4 = Some (OpImm ALU_ADD 11 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fff8 : bv 32 := 0x04578c63.
Lemma F_5fff8 : fetch_word AsanUbsan.M.loaded_segments (0x60040 : word) = Some W_5fff8.
Proof. vm_refl. Qed.
Lemma D_5fff8 : decode_any W_5fff8 = Some (Branch BC_EQ 15 5 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fffc : bv 32 := 0x05078063.
Lemma F_5fffc : fetch_word AsanUbsan.M.loaded_segments (0x60044 : word) = Some W_5fffc.
Proof. vm_refl. Qed.
Lemma D_5fffc : decode_any W_5fffc = Some (Branch BC_EQ 15 16 64, 4%Z).
Proof. vm_refl. Qed.

