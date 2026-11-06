(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_5f444 : bv 32 := 0xff010113.
Lemma F_5f444 : fetch_word AsanUbsan.M.loaded_segments (0x5f494 : word) = Some W_5f444.
Proof. vm_refl. Qed.
Lemma D_5f444 : decode_any W_5f444 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f448 : bv 32 := 0x00113423.
Lemma F_5f448 : fetch_word AsanUbsan.M.loaded_segments (0x5f498 : word) = Some W_5f448.
Proof. vm_refl. Qed.
Lemma D_5f448 : decode_any W_5f448 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f44c : bv 32 := 0x00813023.
Lemma F_5f44c : fetch_word AsanUbsan.M.loaded_segments (0x5f49c : word) = Some W_5f44c.
Proof. vm_refl. Qed.
Lemma D_5f44c : decode_any W_5f44c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f450 : bv 32 := 0x7f853583.
Lemma F_5f450 : fetch_word AsanUbsan.M.loaded_segments (0x5f4a0 : word) = Some W_5f450.
Proof. vm_refl. Qed.
Lemma D_5f450 : decode_any W_5f450 = Some (Load SZ8 true 11 10 2040, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f454 : bv 32 := 0x00000413.
Lemma F_5f454 : fetch_word AsanUbsan.M.loaded_segments (0x5f4a4 : word) = Some W_5f454.
Proof. vm_refl. Qed.
Lemma D_5f454 : decode_any W_5f454 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f458 : bv 32 := 0x00058023.
Lemma F_5f458 : fetch_word AsanUbsan.M.loaded_segments (0x5f4a8 : word) = Some W_5f458.
Proof. vm_refl. Qed.
Lemma D_5f458 : decode_any W_5f458 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f45c : bv 32 := 0x09c000ef.
Lemma F_5f45c : fetch_word AsanUbsan.M.loaded_segments (0x5f4ac : word) = Some W_5f45c.
Proof. vm_refl. Qed.
Lemma D_5f45c : decode_any W_5f45c = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f460 : bv 32 := 0xfffb1597.
Lemma F_5f460 : fetch_word AsanUbsan.M.loaded_segments (0x5f4b0 : word) = Some W_5f460.
Proof. vm_refl. Qed.
Lemma D_5f460 : decode_any W_5f460 = Some (Auipc 11 1048497, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f464 : bv 32 := 0xee85b583.
Lemma F_5f464 : fetch_word AsanUbsan.M.loaded_segments (0x5f4b4 : word) = Some W_5f464.
Proof. vm_refl. Qed.
Lemma D_5f464 : decode_any W_5f464 = Some (Load SZ8 true 11 11 3816, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f468 : bv 32 := 0x00b53023.
Lemma F_5f468 : fetch_word AsanUbsan.M.loaded_segments (0x5f4b8 : word) = Some W_5f468.
Proof. vm_refl. Qed.
Lemma D_5f468 : decode_any W_5f468 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f46c : bv 32 := 0x00b53423.
Lemma F_5f46c : fetch_word AsanUbsan.M.loaded_segments (0x5f4bc : word) = Some W_5f46c.
Proof. vm_refl. Qed.
Lemma D_5f46c : decode_any W_5f46c = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f470 : bv 32 := 0x00b53823.
Lemma F_5f470 : fetch_word AsanUbsan.M.loaded_segments (0x5f4c0 : word) = Some W_5f470.
Proof. vm_refl. Qed.
Lemma D_5f470 : decode_any W_5f470 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f474 : bv 32 := 0x00b53c23.
Lemma F_5f474 : fetch_word AsanUbsan.M.loaded_segments (0x5f4c4 : word) = Some W_5f474.
Proof. vm_refl. Qed.
Lemma D_5f474 : decode_any W_5f474 = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f478 : bv 32 := 0x02b53023.
Lemma F_5f478 : fetch_word AsanUbsan.M.loaded_segments (0x5f4c8 : word) = Some W_5f478.
Proof. vm_refl. Qed.
Lemma D_5f478 : decode_any W_5f478 = Some (Store SZ8 10 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f47c : bv 32 := 0x02b53423.
Lemma F_5f47c : fetch_word AsanUbsan.M.loaded_segments (0x5f4cc : word) = Some W_5f47c.
Proof. vm_refl. Qed.
Lemma D_5f47c : decode_any W_5f47c = Some (Store SZ8 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f480 : bv 32 := 0x02b53823.
Lemma F_5f480 : fetch_word AsanUbsan.M.loaded_segments (0x5f4d0 : word) = Some W_5f480.
Proof. vm_refl. Qed.
Lemma D_5f480 : decode_any W_5f480 = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f484 : bv 32 := 0x02b53c23.
Lemma F_5f484 : fetch_word AsanUbsan.M.loaded_segments (0x5f4d4 : word) = Some W_5f484.
Proof. vm_refl. Qed.
Lemma D_5f484 : decode_any W_5f484 = Some (Store SZ8 10 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f488 : bv 32 := 0x04b53023.
Lemma F_5f488 : fetch_word AsanUbsan.M.loaded_segments (0x5f4d8 : word) = Some W_5f488.
Proof. vm_refl. Qed.
Lemma D_5f488 : decode_any W_5f488 = Some (Store SZ8 10 11 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f48c : bv 32 := 0x04b53423.
Lemma F_5f48c : fetch_word AsanUbsan.M.loaded_segments (0x5f4dc : word) = Some W_5f48c.
Proof. vm_refl. Qed.
Lemma D_5f48c : decode_any W_5f48c = Some (Store SZ8 10 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f490 : bv 32 := 0x04b53823.
Lemma F_5f490 : fetch_word AsanUbsan.M.loaded_segments (0x5f4e0 : word) = Some W_5f490.
Proof. vm_refl. Qed.
Lemma D_5f490 : decode_any W_5f490 = Some (Store SZ8 10 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f494 : bv 32 := 0x04b53c23.
Lemma F_5f494 : fetch_word AsanUbsan.M.loaded_segments (0x5f4e4 : word) = Some W_5f494.
Proof. vm_refl. Qed.
Lemma D_5f494 : decode_any W_5f494 = Some (Store SZ8 10 11 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f498 : bv 32 := 0x06b53023.
Lemma F_5f498 : fetch_word AsanUbsan.M.loaded_segments (0x5f4e8 : word) = Some W_5f498.
Proof. vm_refl. Qed.
Lemma D_5f498 : decode_any W_5f498 = Some (Store SZ8 10 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f49c : bv 32 := 0x06b53423.
Lemma F_5f49c : fetch_word AsanUbsan.M.loaded_segments (0x5f4ec : word) = Some W_5f49c.
Proof. vm_refl. Qed.
Lemma D_5f49c : decode_any W_5f49c = Some (Store SZ8 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4a0 : bv 32 := 0x06b53823.
Lemma F_5f4a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f4f0 : word) = Some W_5f4a0.
Proof. vm_refl. Qed.
Lemma D_5f4a0 : decode_any W_5f4a0 = Some (Store SZ8 10 11 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4a4 : bv 32 := 0x06b53c23.
Lemma F_5f4a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f4f4 : word) = Some W_5f4a4.
Proof. vm_refl. Qed.
Lemma D_5f4a4 : decode_any W_5f4a4 = Some (Store SZ8 10 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4a8 : bv 32 := 0x08b53023.
Lemma F_5f4a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f4f8 : word) = Some W_5f4a8.
Proof. vm_refl. Qed.
Lemma D_5f4a8 : decode_any W_5f4a8 = Some (Store SZ8 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4ac : bv 32 := 0x08b53423.
Lemma F_5f4ac : fetch_word AsanUbsan.M.loaded_segments (0x5f4fc : word) = Some W_5f4ac.
Proof. vm_refl. Qed.
Lemma D_5f4ac : decode_any W_5f4ac = Some (Store SZ8 10 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4b0 : bv 32 := 0x08b53823.
Lemma F_5f4b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f500 : word) = Some W_5f4b0.
Proof. vm_refl. Qed.
Lemma D_5f4b0 : decode_any W_5f4b0 = Some (Store SZ8 10 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4b4 : bv 32 := 0x08b53c23.
Lemma F_5f4b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f504 : word) = Some W_5f4b4.
Proof. vm_refl. Qed.
Lemma D_5f4b4 : decode_any W_5f4b4 = Some (Store SZ8 10 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4b8 : bv 32 := 0x0ab53023.
Lemma F_5f4b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f508 : word) = Some W_5f4b8.
Proof. vm_refl. Qed.
Lemma D_5f4b8 : decode_any W_5f4b8 = Some (Store SZ8 10 11 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4bc : bv 32 := 0x0ab53423.
Lemma F_5f4bc : fetch_word AsanUbsan.M.loaded_segments (0x5f50c : word) = Some W_5f4bc.
Proof. vm_refl. Qed.
Lemma D_5f4bc : decode_any W_5f4bc = Some (Store SZ8 10 11 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4c0 : bv 32 := 0x0ab53823.
Lemma F_5f4c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f510 : word) = Some W_5f4c0.
Proof. vm_refl. Qed.
Lemma D_5f4c0 : decode_any W_5f4c0 = Some (Store SZ8 10 11 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4c4 : bv 32 := 0x0ab53c23.
Lemma F_5f4c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f514 : word) = Some W_5f4c4.
Proof. vm_refl. Qed.
Lemma D_5f4c4 : decode_any W_5f4c4 = Some (Store SZ8 10 11 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4c8 : bv 32 := 0x0cb53023.
Lemma F_5f4c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f518 : word) = Some W_5f4c8.
Proof. vm_refl. Qed.
Lemma D_5f4c8 : decode_any W_5f4c8 = Some (Store SZ8 10 11 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4cc : bv 32 := 0x0cb53423.
Lemma F_5f4cc : fetch_word AsanUbsan.M.loaded_segments (0x5f51c : word) = Some W_5f4cc.
Proof. vm_refl. Qed.
Lemma D_5f4cc : decode_any W_5f4cc = Some (Store SZ8 10 11 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4d0 : bv 32 := 0x0cb53823.
Lemma F_5f4d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f520 : word) = Some W_5f4d0.
Proof. vm_refl. Qed.
Lemma D_5f4d0 : decode_any W_5f4d0 = Some (Store SZ8 10 11 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4d4 : bv 32 := 0x0cb53c23.
Lemma F_5f4d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f524 : word) = Some W_5f4d4.
Proof. vm_refl. Qed.
Lemma D_5f4d4 : decode_any W_5f4d4 = Some (Store SZ8 10 11 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4d8 : bv 32 := 0x0eb53023.
Lemma F_5f4d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f528 : word) = Some W_5f4d8.
Proof. vm_refl. Qed.
Lemma D_5f4d8 : decode_any W_5f4d8 = Some (Store SZ8 10 11 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4dc : bv 32 := 0x0eb53423.
Lemma F_5f4dc : fetch_word AsanUbsan.M.loaded_segments (0x5f52c : word) = Some W_5f4dc.
Proof. vm_refl. Qed.
Lemma D_5f4dc : decode_any W_5f4dc = Some (Store SZ8 10 11 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4e0 : bv 32 := 0x0eb53823.
Lemma F_5f4e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f530 : word) = Some W_5f4e0.
Proof. vm_refl. Qed.
Lemma D_5f4e0 : decode_any W_5f4e0 = Some (Store SZ8 10 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4e4 : bv 32 := 0x0eb53c23.
Lemma F_5f4e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f534 : word) = Some W_5f4e4.
Proof. vm_refl. Qed.
Lemma D_5f4e4 : decode_any W_5f4e4 = Some (Store SZ8 10 11 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4e8 : bv 32 := 0x00813083.
Lemma F_5f4e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f538 : word) = Some W_5f4e8.
Proof. vm_refl. Qed.
Lemma D_5f4e8 : decode_any W_5f4e8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4ec : bv 32 := 0x00013403.
Lemma F_5f4ec : fetch_word AsanUbsan.M.loaded_segments (0x5f53c : word) = Some W_5f4ec.
Proof. vm_refl. Qed.
Lemma D_5f4ec : decode_any W_5f4ec = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4f0 : bv 32 := 0x01010113.
Lemma F_5f4f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f540 : word) = Some W_5f4f0.
Proof. vm_refl. Qed.
Lemma D_5f4f0 : decode_any W_5f4f0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4f4 : bv 32 := 0x00008067.
Lemma F_5f4f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f544 : word) = Some W_5f4f4.
Proof. vm_refl. Qed.
Lemma D_5f4f4 : decode_any W_5f4f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
