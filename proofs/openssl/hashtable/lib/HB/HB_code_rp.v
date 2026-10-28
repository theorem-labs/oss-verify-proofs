(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1c5060 : bv 32 := 0x0041f597.
Lemma F_1c5060 : fetch_word AsanUbsan.M.loaded_segments (0x1c0030 : word) = Some W_1c5060.
Proof. vm_refl. Qed.
Lemma D_1c5060 : decode_any W_1c5060 = Some (Auipc 11 1055, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5064 : bv 32 := 0xaa85b583.
Lemma F_1c5064 : fetch_word AsanUbsan.M.loaded_segments (0x1c0034 : word) = Some W_1c5064.
Proof. vm_refl. Qed.
Lemma D_1c5064 : decode_any W_1c5064 = Some (Load SZ8 true 11 11 2728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5068 : bv 32 := 0x0005b583.
Lemma F_1c5068 : fetch_word AsanUbsan.M.loaded_segments (0x1c0038 : word) = Some W_1c5068.
Proof. vm_refl. Qed.
Lemma D_1c5068 : decode_any W_1c5068 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c506c : bv 32 := 0xfff58613.
Lemma F_1c506c : fetch_word AsanUbsan.M.loaded_segments (0x1c003c : word) = Some W_1c506c.
Proof. vm_refl. Qed.
Lemma D_1c506c : decode_any W_1c506c = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5070 : bv 32 := 0x00c5b6b3.
Lemma F_1c5070 : fetch_word AsanUbsan.M.loaded_segments (0x1c0040 : word) = Some W_1c5070.
Proof. vm_refl. Qed.
Lemma D_1c5070 : decode_any W_1c5070 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5074 : bv 32 := 0xfff68693.
Lemma F_1c5074 : fetch_word AsanUbsan.M.loaded_segments (0x1c0044 : word) = Some W_1c5074.
Proof. vm_refl. Qed.
Lemma D_1c5074 : decode_any W_1c5074 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5078 : bv 32 := 0x00c6f6b3.
Lemma F_1c5078 : fetch_word AsanUbsan.M.loaded_segments (0x1c0048 : word) = Some W_1c5078.
Proof. vm_refl. Qed.
Lemma D_1c5078 : decode_any W_1c5078 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c507c : bv 32 := 0x04a6f263.
Lemma F_1c507c : fetch_word AsanUbsan.M.loaded_segments (0x1c004c : word) = Some W_1c507c.
Proof. vm_refl. Qed.
Lemma D_1c507c : decode_any W_1c507c = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5080 : bv 32 := 0x0041f697.
Lemma F_1c5080 : fetch_word AsanUbsan.M.loaded_segments (0x1c0050 : word) = Some W_1c5080.
Proof. vm_refl. Qed.
Lemma D_1c5080 : decode_any W_1c5080 = Some (Auipc 13 1055, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5084 : bv 32 := 0xa906b683.
Lemma F_1c5084 : fetch_word AsanUbsan.M.loaded_segments (0x1c0054 : word) = Some W_1c5084.
Proof. vm_refl. Qed.
Lemma D_1c5084 : decode_any W_1c5084 = Some (Load SZ8 true 13 13 2704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5088 : bv 32 := 0x0041f717.
Lemma F_1c5088 : fetch_word AsanUbsan.M.loaded_segments (0x1c0058 : word) = Some W_1c5088.
Proof. vm_refl. Qed.
Lemma D_1c5088 : decode_any W_1c5088 = Some (Auipc 14 1055, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c508c : bv 32 := 0xa9073703.
Lemma F_1c508c : fetch_word AsanUbsan.M.loaded_segments (0x1c005c : word) = Some W_1c508c.
Proof. vm_refl. Qed.
Lemma D_1c508c : decode_any W_1c508c = Some (Load SZ8 true 14 14 2704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5090 : bv 32 := 0x0006b803.
Lemma F_1c5090 : fetch_word AsanUbsan.M.loaded_segments (0x1c0060 : word) = Some W_1c5090.
Proof. vm_refl. Qed.
Lemma D_1c5090 : decode_any W_1c5090 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5094 : bv 32 := 0x00073683.
Lemma F_1c5094 : fetch_word AsanUbsan.M.loaded_segments (0x1c0064 : word) = Some W_1c5094.
Proof. vm_refl. Qed.
Lemma D_1c5094 : decode_any W_1c5094 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5098 : bv 32 := 0xfff80793.
Lemma F_1c5098 : fetch_word AsanUbsan.M.loaded_segments (0x1c0068 : word) = Some W_1c5098.
Proof. vm_refl. Qed.
Lemma D_1c5098 : decode_any W_1c5098 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c509c : bv 32 := 0x00a7f463.
Lemma F_1c509c : fetch_word AsanUbsan.M.loaded_segments (0x1c006c : word) = Some W_1c509c.
Proof. vm_refl. Qed.
Lemma D_1c509c : decode_any W_1c509c = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c50a0 : bv 32 := 0x02a6f063.
Lemma F_1c50a0 : fetch_word AsanUbsan.M.loaded_segments (0x1c0070 : word) = Some W_1c50a0.
Proof. vm_refl. Qed.
Lemma D_1c50a0 : decode_any W_1c50a0 = Some (Branch BC_GEU 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c50a4 : bv 32 := 0x0041f717.
Lemma F_1c50a4 : fetch_word AsanUbsan.M.loaded_segments (0x1c0074 : word) = Some W_1c50a4.
Proof. vm_refl. Qed.
Lemma D_1c50a4 : decode_any W_1c50a4 = Some (Auipc 14 1055, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c50a8 : bv 32 := 0xa7c73703.
Lemma F_1c50a8 : fetch_word AsanUbsan.M.loaded_segments (0x1c0078 : word) = Some W_1c50a8.
Proof. vm_refl. Qed.
Lemma D_1c50a8 : decode_any W_1c50a8 = Some (Load SZ8 true 14 14 2684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c50ac : bv 32 := 0x00073283.
Lemma F_1c50ac : fetch_word AsanUbsan.M.loaded_segments (0x1c007c : word) = Some W_1c50ac.
Proof. vm_refl. Qed.
Lemma D_1c50ac : decode_any W_1c50ac = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c50b0 : bv 32 := 0x0032d713.
Lemma F_1c50b0 : fetch_word AsanUbsan.M.loaded_segments (0x1c0080 : word) = Some W_1c50b0.
Proof. vm_refl. Qed.
Lemma D_1c50b0 : decode_any W_1c50b0 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c50b4 : bv 32 := 0x00b708b3.
Lemma F_1c50b4 : fetch_word AsanUbsan.M.loaded_segments (0x1c0084 : word) = Some W_1c50b4.
Proof. vm_refl. Qed.
Lemma D_1c50b4 : decode_any W_1c50b4 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c50b8 : bv 32 := 0x00a2ea63.
Lemma F_1c50b8 : fetch_word AsanUbsan.M.loaded_segments (0x1c0088 : word) = Some W_1c50b8.
Proof. vm_refl. Qed.
Lemma D_1c50b8 : decode_any W_1c50b8 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c50bc : bv 32 := 0x00a8f863.
Lemma F_1c50bc : fetch_word AsanUbsan.M.loaded_segments (0x1c008c : word) = Some W_1c50bc.
Proof. vm_refl. Qed.
Lemma D_1c50bc : decode_any W_1c50bc = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c50c0 : bv 32 := 0x00355513.
Lemma F_1c50c0 : fetch_word AsanUbsan.M.loaded_segments (0x1c0090 : word) = Some W_1c50c0.
Proof. vm_refl. Qed.
Lemma D_1c50c0 : decode_any W_1c50c0 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c50c4 : bv 32 := 0x00a58533.
Lemma F_1c50c4 : fetch_word AsanUbsan.M.loaded_segments (0x1c0094 : word) = Some W_1c50c4.
Proof. vm_refl. Qed.
Lemma D_1c50c4 : decode_any W_1c50c4 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c50c8 : bv 32 := 0x00008067.
Lemma F_1c50c8 : fetch_word AsanUbsan.M.loaded_segments (0x1c0098 : word) = Some W_1c50c8.
Proof. vm_refl. Qed.
Lemma D_1c50c8 : decode_any W_1c50c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c54ec : bv 32 := 0xfc010113.
Lemma F_1c54ec : fetch_word AsanUbsan.M.loaded_segments (0x1c04bc : word) = Some W_1c54ec.
Proof. vm_refl. Qed.
Lemma D_1c54ec : decode_any W_1c54ec = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c54f0 : bv 32 := 0x02113c23.
Lemma F_1c54f0 : fetch_word AsanUbsan.M.loaded_segments (0x1c04c0 : word) = Some W_1c54f0.
Proof. vm_refl. Qed.
Lemma D_1c54f0 : decode_any W_1c54f0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c54f4 : bv 32 := 0x02813823.
Lemma F_1c54f4 : fetch_word AsanUbsan.M.loaded_segments (0x1c04c4 : word) = Some W_1c54f4.
Proof. vm_refl. Qed.
Lemma D_1c54f4 : decode_any W_1c54f4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c54f8 : bv 32 := 0x02913423.
Lemma F_1c54f8 : fetch_word AsanUbsan.M.loaded_segments (0x1c04c8 : word) = Some W_1c54f8.
Proof. vm_refl. Qed.
Lemma D_1c54f8 : decode_any W_1c54f8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c54fc : bv 32 := 0x03213023.
Lemma F_1c54fc : fetch_word AsanUbsan.M.loaded_segments (0x1c04cc : word) = Some W_1c54fc.
Proof. vm_refl. Qed.
Lemma D_1c54fc : decode_any W_1c54fc = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5500 : bv 32 := 0x01313c23.
Lemma F_1c5500 : fetch_word AsanUbsan.M.loaded_segments (0x1c04d0 : word) = Some W_1c5500.
Proof. vm_refl. Qed.
Lemma D_1c5500 : decode_any W_1c5500 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5504 : bv 32 := 0x01413823.
Lemma F_1c5504 : fetch_word AsanUbsan.M.loaded_segments (0x1c04d4 : word) = Some W_1c5504.
Proof. vm_refl. Qed.
Lemma D_1c5504 : decode_any W_1c5504 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5508 : bv 32 := 0x01513423.
Lemma F_1c5508 : fetch_word AsanUbsan.M.loaded_segments (0x1c04d8 : word) = Some W_1c5508.
Proof. vm_refl. Qed.
Lemma D_1c5508 : decode_any W_1c5508 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c550c : bv 32 := 0x14058c63.
Lemma F_1c550c : fetch_word AsanUbsan.M.loaded_segments (0x1c04dc : word) = Some W_1c550c.
Proof. vm_refl. Qed.
Lemma D_1c550c : decode_any W_1c550c = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5510 : bv 32 := 0x00058493.
Lemma F_1c5510 : fetch_word AsanUbsan.M.loaded_segments (0x1c04e0 : word) = Some W_1c5510.
Proof. vm_refl. Qed.
Lemma D_1c5510 : decode_any W_1c5510 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5514 : bv 32 := 0x00050413.
Lemma F_1c5514 : fetch_word AsanUbsan.M.loaded_segments (0x1c04e4 : word) = Some W_1c5514.
Proof. vm_refl. Qed.
Lemma D_1c5514 : decode_any W_1c5514 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5518 : bv 32 := 0x0041e517.
Lemma F_1c5518 : fetch_word AsanUbsan.M.loaded_segments (0x1c04e8 : word) = Some W_1c5518.
Proof. vm_refl. Qed.
Lemma D_1c5518 : decode_any W_1c5518 = Some (Auipc 10 1054, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c551c : bv 32 := 0x5f053a83.
Lemma F_1c551c : fetch_word AsanUbsan.M.loaded_segments (0x1c04ec : word) = Some W_1c551c.
Proof. vm_refl. Qed.
Lemma D_1c551c : decode_any W_1c551c = Some (Load SZ8 true 21 10 1520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5520 : bv 32 := 0x000ab583.
Lemma F_1c5520 : fetch_word AsanUbsan.M.loaded_segments (0x1c04f0 : word) = Some W_1c5520.
Proof. vm_refl. Qed.
Lemma D_1c5520 : decode_any W_1c5520 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5524 : bv 32 := 0xfff58513.
Lemma F_1c5524 : fetch_word AsanUbsan.M.loaded_segments (0x1c04f4 : word) = Some W_1c5524.
Proof. vm_refl. Qed.
Lemma D_1c5524 : decode_any W_1c5524 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5528 : bv 32 := 0x00a5b633.
Lemma F_1c5528 : fetch_word AsanUbsan.M.loaded_segments (0x1c04f8 : word) = Some W_1c5528.
Proof. vm_refl. Qed.
Lemma D_1c5528 : decode_any W_1c5528 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c552c : bv 32 := 0xfff60613.
Lemma F_1c552c : fetch_word AsanUbsan.M.loaded_segments (0x1c04fc : word) = Some W_1c552c.
Proof. vm_refl. Qed.
Lemma D_1c552c : decode_any W_1c552c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5530 : bv 32 := 0x00a67633.
Lemma F_1c5530 : fetch_word AsanUbsan.M.loaded_segments (0x1c0500 : word) = Some W_1c5530.
Proof. vm_refl. Qed.
Lemma D_1c5530 : decode_any W_1c5530 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5534 : bv 32 := 0x04867263.
Lemma F_1c5534 : fetch_word AsanUbsan.M.loaded_segments (0x1c0504 : word) = Some W_1c5534.
Proof. vm_refl. Qed.
Lemma D_1c5534 : decode_any W_1c5534 = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5538 : bv 32 := 0x0041e697.
Lemma F_1c5538 : fetch_word AsanUbsan.M.loaded_segments (0x1c0508 : word) = Some W_1c5538.
Proof. vm_refl. Qed.
Lemma D_1c5538 : decode_any W_1c5538 = Some (Auipc 13 1054, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c553c : bv 32 := 0x5d86b683.
Lemma F_1c553c : fetch_word AsanUbsan.M.loaded_segments (0x1c050c : word) = Some W_1c553c.
Proof. vm_refl. Qed.
Lemma D_1c553c : decode_any W_1c553c = Some (Load SZ8 true 13 13 1496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5540 : bv 32 := 0x0041e717.
Lemma F_1c5540 : fetch_word AsanUbsan.M.loaded_segments (0x1c0510 : word) = Some W_1c5540.
Proof. vm_refl. Qed.
Lemma D_1c5540 : decode_any W_1c5540 = Some (Auipc 14 1054, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5544 : bv 32 := 0x5d873703.
Lemma F_1c5544 : fetch_word AsanUbsan.M.loaded_segments (0x1c0514 : word) = Some W_1c5544.
Proof. vm_refl. Qed.
Lemma D_1c5544 : decode_any W_1c5544 = Some (Load SZ8 true 14 14 1496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5548 : bv 32 := 0x0006b803.
Lemma F_1c5548 : fetch_word AsanUbsan.M.loaded_segments (0x1c0518 : word) = Some W_1c5548.
Proof. vm_refl. Qed.
Lemma D_1c5548 : decode_any W_1c5548 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c554c : bv 32 := 0x00073683.
Lemma F_1c554c : fetch_word AsanUbsan.M.loaded_segments (0x1c051c : word) = Some W_1c554c.
Proof. vm_refl. Qed.
Lemma D_1c554c : decode_any W_1c554c = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5550 : bv 32 := 0xfff80793.
Lemma F_1c5550 : fetch_word AsanUbsan.M.loaded_segments (0x1c0520 : word) = Some W_1c5550.
Proof. vm_refl. Qed.
Lemma D_1c5550 : decode_any W_1c5550 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5554 : bv 32 := 0x0087f463.
Lemma F_1c5554 : fetch_word AsanUbsan.M.loaded_segments (0x1c0524 : word) = Some W_1c5554.
Proof. vm_refl. Qed.
Lemma D_1c5554 : decode_any W_1c5554 = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5558 : bv 32 := 0x0286f063.
Lemma F_1c5558 : fetch_word AsanUbsan.M.loaded_segments (0x1c0528 : word) = Some W_1c5558.
Proof. vm_refl. Qed.
Lemma D_1c5558 : decode_any W_1c5558 = Some (Branch BC_GEU 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c555c : bv 32 := 0x0041e717.
Lemma F_1c555c : fetch_word AsanUbsan.M.loaded_segments (0x1c052c : word) = Some W_1c555c.
Proof. vm_refl. Qed.
Lemma D_1c555c : decode_any W_1c555c = Some (Auipc 14 1054, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5560 : bv 32 := 0x5c473703.
Lemma F_1c5560 : fetch_word AsanUbsan.M.loaded_segments (0x1c0530 : word) = Some W_1c5560.
Proof. vm_refl. Qed.
Lemma D_1c5560 : decode_any W_1c5560 = Some (Load SZ8 true 14 14 1476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5564 : bv 32 := 0x00073283.
Lemma F_1c5564 : fetch_word AsanUbsan.M.loaded_segments (0x1c0534 : word) = Some W_1c5564.
Proof. vm_refl. Qed.
Lemma D_1c5564 : decode_any W_1c5564 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5568 : bv 32 := 0x0032d713.
Lemma F_1c5568 : fetch_word AsanUbsan.M.loaded_segments (0x1c0538 : word) = Some W_1c5568.
Proof. vm_refl. Qed.
Lemma D_1c5568 : decode_any W_1c5568 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c556c : bv 32 := 0x00b708b3.
Lemma F_1c556c : fetch_word AsanUbsan.M.loaded_segments (0x1c053c : word) = Some W_1c556c.
Proof. vm_refl. Qed.
Lemma D_1c556c : decode_any W_1c556c = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5570 : bv 32 := 0x1282e063.
Lemma F_1c5570 : fetch_word AsanUbsan.M.loaded_segments (0x1c0540 : word) = Some W_1c5570.
Proof. vm_refl. Qed.
Lemma D_1c5570 : decode_any W_1c5570 = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5574 : bv 32 := 0x1088fe63.
Lemma F_1c5574 : fetch_word AsanUbsan.M.loaded_segments (0x1c0544 : word) = Some W_1c5574.
Proof. vm_refl. Qed.
Lemma D_1c5574 : decode_any W_1c5574 = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5578 : bv 32 := 0x00848933.
Lemma F_1c5578 : fetch_word AsanUbsan.M.loaded_segments (0x1c0548 : word) = Some W_1c5578.
Proof. vm_refl. Qed.
Lemma D_1c5578 : decode_any W_1c5578 = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c557c : bv 32 := 0x05267263.
Lemma F_1c557c : fetch_word AsanUbsan.M.loaded_segments (0x1c054c : word) = Some W_1c557c.
Proof. vm_refl. Qed.
Lemma D_1c557c : decode_any W_1c557c = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5580 : bv 32 := 0x0041e617.
Lemma F_1c5580 : fetch_word AsanUbsan.M.loaded_segments (0x1c0550 : word) = Some W_1c5580.
Proof. vm_refl. Qed.
Lemma D_1c5580 : decode_any W_1c5580 = Some (Auipc 12 1054, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5584 : bv 32 := 0x59063603.
Lemma F_1c5584 : fetch_word AsanUbsan.M.loaded_segments (0x1c0554 : word) = Some W_1c5584.
Proof. vm_refl. Qed.
Lemma D_1c5584 : decode_any W_1c5584 = Some (Load SZ8 true 12 12 1424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5588 : bv 32 := 0x0041e697.
Lemma F_1c5588 : fetch_word AsanUbsan.M.loaded_segments (0x1c0558 : word) = Some W_1c5588.
Proof. vm_refl. Qed.
Lemma D_1c5588 : decode_any W_1c5588 = Some (Auipc 13 1054, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c558c : bv 32 := 0x5906b683.
Lemma F_1c558c : fetch_word AsanUbsan.M.loaded_segments (0x1c055c : word) = Some W_1c558c.
Proof. vm_refl. Qed.
Lemma D_1c558c : decode_any W_1c558c = Some (Load SZ8 true 13 13 1424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5590 : bv 32 := 0x00063783.
Lemma F_1c5590 : fetch_word AsanUbsan.M.loaded_segments (0x1c0560 : word) = Some W_1c5590.
Proof. vm_refl. Qed.
Lemma D_1c5590 : decode_any W_1c5590 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5594 : bv 32 := 0x0006b603.
Lemma F_1c5594 : fetch_word AsanUbsan.M.loaded_segments (0x1c0564 : word) = Some W_1c5594.
Proof. vm_refl. Qed.
Lemma D_1c5594 : decode_any W_1c5594 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5598 : bv 32 := 0xfff78713.
Lemma F_1c5598 : fetch_word AsanUbsan.M.loaded_segments (0x1c0568 : word) = Some W_1c5598.
Proof. vm_refl. Qed.
Lemma D_1c5598 : decode_any W_1c5598 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c559c : bv 32 := 0x01277463.
Lemma F_1c559c : fetch_word AsanUbsan.M.loaded_segments (0x1c056c : word) = Some W_1c559c.
Proof. vm_refl. Qed.
Lemma D_1c559c : decode_any W_1c559c = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55a0 : bv 32 := 0x03267063.
Lemma F_1c55a0 : fetch_word AsanUbsan.M.loaded_segments (0x1c0570 : word) = Some W_1c55a0.
Proof. vm_refl. Qed.
Lemma D_1c55a0 : decode_any W_1c55a0 = Some (Branch BC_GEU 12 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55a4 : bv 32 := 0x0041e697.
Lemma F_1c55a4 : fetch_word AsanUbsan.M.loaded_segments (0x1c0574 : word) = Some W_1c55a4.
Proof. vm_refl. Qed.
Lemma D_1c55a4 : decode_any W_1c55a4 = Some (Auipc 13 1054, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55a8 : bv 32 := 0x57c6b683.
Lemma F_1c55a8 : fetch_word AsanUbsan.M.loaded_segments (0x1c0578 : word) = Some W_1c55a8.
Proof. vm_refl. Qed.
Lemma D_1c55a8 : decode_any W_1c55a8 = Some (Load SZ8 true 13 13 1404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55ac : bv 32 := 0x0006b883.
Lemma F_1c55ac : fetch_word AsanUbsan.M.loaded_segments (0x1c057c : word) = Some W_1c55ac.
Proof. vm_refl. Qed.
Lemma D_1c55ac : decode_any W_1c55ac = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55b0 : bv 32 := 0x0038d693.
Lemma F_1c55b0 : fetch_word AsanUbsan.M.loaded_segments (0x1c0580 : word) = Some W_1c55b0.
Proof. vm_refl. Qed.
Lemma D_1c55b0 : decode_any W_1c55b0 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55b4 : bv 32 := 0x00b68833.
Lemma F_1c55b4 : fetch_word AsanUbsan.M.loaded_segments (0x1c0584 : word) = Some W_1c55b4.
Proof. vm_refl. Qed.
Lemma D_1c55b4 : decode_any W_1c55b4 = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55b8 : bv 32 := 0x1328e463.
Lemma F_1c55b8 : fetch_word AsanUbsan.M.loaded_segments (0x1c0588 : word) = Some W_1c55b8.
Proof. vm_refl. Qed.
Lemma D_1c55b8 : decode_any W_1c55b8 = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55bc : bv 32 := 0x13287263.
Lemma F_1c55bc : fetch_word AsanUbsan.M.loaded_segments (0x1c058c : word) = Some W_1c55bc.
Proof. vm_refl. Qed.
Lemma D_1c55bc : decode_any W_1c55bc = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55c0 : bv 32 := 0x23247863.
Lemma F_1c55c0 : fetch_word AsanUbsan.M.loaded_segments (0x1c0590 : word) = Some W_1c55c0.
Proof. vm_refl. Qed.
Lemma D_1c55c0 : decode_any W_1c55c0 = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55c4 : bv 32 := 0x00740513.
Lemma F_1c55c4 : fetch_word AsanUbsan.M.loaded_segments (0x1c0594 : word) = Some W_1c55c4.
Proof. vm_refl. Qed.
Lemma D_1c55c4 : decode_any W_1c55c4 = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55c8 : bv 32 := 0xff857513.
Lemma F_1c55c8 : fetch_word AsanUbsan.M.loaded_segments (0x1c0598 : word) = Some W_1c55c8.
Proof. vm_refl. Qed.
Lemma D_1c55c8 : decode_any W_1c55c8 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55cc : bv 32 := 0xff897a13.
Lemma F_1c55cc : fetch_word AsanUbsan.M.loaded_segments (0x1c059c : word) = Some W_1c55cc.
Proof. vm_refl. Qed.
Lemma D_1c55cc : decode_any W_1c55cc = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55d0 : bv 32 := 0xa91ff0ef.
Lemma F_1c55d0 : fetch_word AsanUbsan.M.loaded_segments (0x1c05a0 : word) = Some W_1c55d0.
Proof. vm_refl. Qed.
Lemma D_1c55d0 : decode_any W_1c55d0 = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55d4 : bv 32 := 0x00050993.
Lemma F_1c55d4 : fetch_word AsanUbsan.M.loaded_segments (0x1c05a4 : word) = Some W_1c55d4.
Proof. vm_refl. Qed.
Lemma D_1c55d4 : decode_any W_1c55d4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55d8 : bv 32 := 0x000a0513.
Lemma F_1c55d8 : fetch_word AsanUbsan.M.loaded_segments (0x1c05a8 : word) = Some W_1c55d8.
Proof. vm_refl. Qed.
Lemma D_1c55d8 : decode_any W_1c55d8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55dc : bv 32 := 0xa85ff0ef.
Lemma F_1c55dc : fetch_word AsanUbsan.M.loaded_segments (0x1c05ac : word) = Some W_1c55dc.
Proof. vm_refl. Qed.
Lemma D_1c55dc : decode_any W_1c55dc = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55e0 : bv 32 := 0x000ab583.
Lemma F_1c55e0 : fetch_word AsanUbsan.M.loaded_segments (0x1c05b0 : word) = Some W_1c55e0.
Proof. vm_refl. Qed.
Lemma D_1c55e0 : decode_any W_1c55e0 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55e4 : bv 32 := 0x00345613.
Lemma F_1c55e4 : fetch_word AsanUbsan.M.loaded_segments (0x1c05b4 : word) = Some W_1c55e4.
Proof. vm_refl. Qed.
Lemma D_1c55e4 : decode_any W_1c55e4 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55e8 : bv 32 := 0x00c58633.
Lemma F_1c55e8 : fetch_word AsanUbsan.M.loaded_segments (0x1c05b8 : word) = Some W_1c55e8.
Proof. vm_refl. Qed.
Lemma D_1c55e8 : decode_any W_1c55e8 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55ec : bv 32 := 0x00060603.
Lemma F_1c55ec : fetch_word AsanUbsan.M.loaded_segments (0x1c05bc : word) = Some W_1c55ec.
Proof. vm_refl. Qed.
Lemma D_1c55ec : decode_any W_1c55ec = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55f0 : bv 32 := 0x00060663.
Lemma F_1c55f0 : fetch_word AsanUbsan.M.loaded_segments (0x1c05c0 : word) = Some W_1c55f0.
Proof. vm_refl. Qed.
Lemma D_1c55f0 : decode_any W_1c55f0 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55f4 : bv 32 := 0x00747693.
Lemma F_1c55f4 : fetch_word AsanUbsan.M.loaded_segments (0x1c05c4 : word) = Some W_1c55f4.
Proof. vm_refl. Qed.
Lemma D_1c55f4 : decode_any W_1c55f4 = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55f8 : bv 32 := 0x02c6d063.
Lemma F_1c55f8 : fetch_word AsanUbsan.M.loaded_segments (0x1c05c8 : word) = Some W_1c55f8.
Proof. vm_refl. Qed.
Lemma D_1c55f8 : decode_any W_1c55f8 = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c55fc : bv 32 := 0xfff90913.
Lemma F_1c55fc : fetch_word AsanUbsan.M.loaded_segments (0x1c05cc : word) = Some W_1c55fc.
Proof. vm_refl. Qed.
Lemma D_1c55fc : decode_any W_1c55fc = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5600 : bv 32 := 0x00395613.
Lemma F_1c5600 : fetch_word AsanUbsan.M.loaded_segments (0x1c05d0 : word) = Some W_1c5600.
Proof. vm_refl. Qed.
Lemma D_1c5600 : decode_any W_1c5600 = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5604 : bv 32 := 0x00c585b3.
Lemma F_1c5604 : fetch_word AsanUbsan.M.loaded_segments (0x1c05d4 : word) = Some W_1c5604.
Proof. vm_refl. Qed.
Lemma D_1c5604 : decode_any W_1c5604 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5608 : bv 32 := 0x00058583.
Lemma F_1c5608 : fetch_word AsanUbsan.M.loaded_segments (0x1c05d8 : word) = Some W_1c5608.
Proof. vm_refl. Qed.
Lemma D_1c5608 : decode_any W_1c5608 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c560c : bv 32 := 0x04058263.
Lemma F_1c560c : fetch_word AsanUbsan.M.loaded_segments (0x1c05dc : word) = Some W_1c560c.
Proof. vm_refl. Qed.
Lemma D_1c560c : decode_any W_1c560c = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5610 : bv 32 := 0x00797613.
Lemma F_1c5610 : fetch_word AsanUbsan.M.loaded_segments (0x1c05e0 : word) = Some W_1c5610.
Proof. vm_refl. Qed.
Lemma D_1c5610 : decode_any W_1c5610 = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5614 : bv 32 := 0x02b64e63.
Lemma F_1c5614 : fetch_word AsanUbsan.M.loaded_segments (0x1c05e4 : word) = Some W_1c5614.
Proof. vm_refl. Qed.
Lemma D_1c5614 : decode_any W_1c5614 = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5618 : bv 32 := 0x000ab503.
Lemma F_1c5618 : fetch_word AsanUbsan.M.loaded_segments (0x1c05e8 : word) = Some W_1c5618.
Proof. vm_refl. Qed.
Lemma D_1c5618 : decode_any W_1c5618 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c561c : bv 32 := 0x00040593.
Lemma F_1c561c : fetch_word AsanUbsan.M.loaded_segments (0x1c05ec : word) = Some W_1c561c.
Proof. vm_refl. Qed.
Lemma D_1c561c : decode_any W_1c561c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5620 : bv 32 := 0x0140006f.
Lemma F_1c5620 : fetch_word AsanUbsan.M.loaded_segments (0x1c05f0 : word) = Some W_1c5620.
Proof. vm_refl. Qed.
Lemma D_1c5620 : decode_any W_1c5620 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5624 : bv 32 := 0x00140413.
Lemma F_1c5624 : fetch_word AsanUbsan.M.loaded_segments (0x1c05f4 : word) = Some W_1c5624.
Proof. vm_refl. Qed.
Lemma D_1c5624 : decode_any W_1c5624 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5628 : bv 32 := 0xfff48493.
Lemma F_1c5628 : fetch_word AsanUbsan.M.loaded_segments (0x1c05f8 : word) = Some W_1c5628.
Proof. vm_refl. Qed.
Lemma D_1c5628 : decode_any W_1c5628 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c562c : bv 32 := 0x00158593.
Lemma F_1c562c : fetch_word AsanUbsan.M.loaded_segments (0x1c05fc : word) = Some W_1c562c.
Proof. vm_refl. Qed.
Lemma D_1c562c : decode_any W_1c562c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5630 : bv 32 := 0x1e048063.
Lemma F_1c5630 : fetch_word AsanUbsan.M.loaded_segments (0x1c0600 : word) = Some W_1c5630.
Proof. vm_refl. Qed.
Lemma D_1c5630 : decode_any W_1c5630 = Some (Branch BC_EQ 9 0 480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5634 : bv 32 := 0x00345613.
Lemma F_1c5634 : fetch_word AsanUbsan.M.loaded_segments (0x1c0604 : word) = Some W_1c5634.
Proof. vm_refl. Qed.
Lemma D_1c5634 : decode_any W_1c5634 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5638 : bv 32 := 0x00c50633.
Lemma F_1c5638 : fetch_word AsanUbsan.M.loaded_segments (0x1c0608 : word) = Some W_1c5638.
Proof. vm_refl. Qed.
Lemma D_1c5638 : decode_any W_1c5638 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c563c : bv 32 := 0x00060603.
Lemma F_1c563c : fetch_word AsanUbsan.M.loaded_segments (0x1c060c : word) = Some W_1c563c.
Proof. vm_refl. Qed.
Lemma D_1c563c : decode_any W_1c563c = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5640 : bv 32 := 0xfe0602e3.
Lemma F_1c5640 : fetch_word AsanUbsan.M.loaded_segments (0x1c0610 : word) = Some W_1c5640.
Proof. vm_refl. Qed.
Lemma D_1c5640 : decode_any W_1c5640 = Some (Branch BC_EQ 12 0 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5644 : bv 32 := 0x0075f693.
Lemma F_1c5644 : fetch_word AsanUbsan.M.loaded_segments (0x1c0614 : word) = Some W_1c5644.
Proof. vm_refl. Qed.
Lemma D_1c5644 : decode_any W_1c5644 = Some (OpImm ALU_AND 13 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5648 : bv 32 := 0xfcc6cee3.
Lemma F_1c5648 : fetch_word AsanUbsan.M.loaded_segments (0x1c0618 : word) = Some W_1c5648.
Proof. vm_refl. Qed.
Lemma D_1c5648 : decode_any W_1c5648 = Some (Branch BC_LT 13 12 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c564c : bv 32 := 0x01c0006f.
Lemma F_1c564c : fetch_word AsanUbsan.M.loaded_segments (0x1c061c : word) = Some W_1c564c.
Proof. vm_refl. Qed.
Lemma D_1c564c : decode_any W_1c564c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5650 : bv 32 := 0x00a9fa63.
Lemma F_1c5650 : fetch_word AsanUbsan.M.loaded_segments (0x1c0620 : word) = Some W_1c5650.
Proof. vm_refl. Qed.
Lemma D_1c5650 : decode_any W_1c5650 = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5654 : bv 32 := 0x413505b3.
Lemma F_1c5654 : fetch_word AsanUbsan.M.loaded_segments (0x1c0624 : word) = Some W_1c5654.
Proof. vm_refl. Qed.
Lemma D_1c5654 : decode_any W_1c5654 = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5658 : bv 32 := 0x00098513.
Lemma F_1c5658 : fetch_word AsanUbsan.M.loaded_segments (0x1c0628 : word) = Some W_1c5658.
Proof. vm_refl. Qed.
Lemma D_1c5658 : decode_any W_1c5658 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c565c : bv 32 := 0x374100ef.
Lemma F_1c565c : fetch_word AsanUbsan.M.loaded_segments (0x1c062c : word) = Some W_1c565c.
Proof. vm_refl. Qed.
Lemma D_1c565c : decode_any W_1c565c = Some (Jal 1 66420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5660 : bv 32 := 0xfa050ce3.
Lemma F_1c5660 : fetch_word AsanUbsan.M.loaded_segments (0x1c0630 : word) = Some W_1c5660.
Proof. vm_refl. Qed.
Lemma D_1c5660 : decode_any W_1c5660 = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5664 : bv 32 := 0x00000413.
Lemma F_1c5664 : fetch_word AsanUbsan.M.loaded_segments (0x1c0634 : word) = Some W_1c5664.
Proof. vm_refl. Qed.
Lemma D_1c5664 : decode_any W_1c5664 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5668 : bv 32 := 0x00040513.
Lemma F_1c5668 : fetch_word AsanUbsan.M.loaded_segments (0x1c0638 : word) = Some W_1c5668.
Proof. vm_refl. Qed.
Lemma D_1c5668 : decode_any W_1c5668 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c566c : bv 32 := 0x03813083.
Lemma F_1c566c : fetch_word AsanUbsan.M.loaded_segments (0x1c063c : word) = Some W_1c566c.
Proof. vm_refl. Qed.
Lemma D_1c566c : decode_any W_1c566c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5670 : bv 32 := 0x03013403.
Lemma F_1c5670 : fetch_word AsanUbsan.M.loaded_segments (0x1c0640 : word) = Some W_1c5670.
Proof. vm_refl. Qed.
Lemma D_1c5670 : decode_any W_1c5670 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5674 : bv 32 := 0x02813483.
Lemma F_1c5674 : fetch_word AsanUbsan.M.loaded_segments (0x1c0644 : word) = Some W_1c5674.
Proof. vm_refl. Qed.
Lemma D_1c5674 : decode_any W_1c5674 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5678 : bv 32 := 0x02013903.
Lemma F_1c5678 : fetch_word AsanUbsan.M.loaded_segments (0x1c0648 : word) = Some W_1c5678.
Proof. vm_refl. Qed.
Lemma D_1c5678 : decode_any W_1c5678 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c567c : bv 32 := 0x01813983.
Lemma F_1c567c : fetch_word AsanUbsan.M.loaded_segments (0x1c064c : word) = Some W_1c567c.
Proof. vm_refl. Qed.
Lemma D_1c567c : decode_any W_1c567c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5680 : bv 32 := 0x01013a03.
Lemma F_1c5680 : fetch_word AsanUbsan.M.loaded_segments (0x1c0650 : word) = Some W_1c5680.
Proof. vm_refl. Qed.
Lemma D_1c5680 : decode_any W_1c5680 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5684 : bv 32 := 0x00813a83.
Lemma F_1c5684 : fetch_word AsanUbsan.M.loaded_segments (0x1c0654 : word) = Some W_1c5684.
Proof. vm_refl. Qed.
Lemma D_1c5684 : decode_any W_1c5684 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5688 : bv 32 := 0x04010113.
Lemma F_1c5688 : fetch_word AsanUbsan.M.loaded_segments (0x1c0658 : word) = Some W_1c5688.
Proof. vm_refl. Qed.
Lemma D_1c5688 : decode_any W_1c5688 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c568c : bv 32 := 0x00008067.
Lemma F_1c568c : fetch_word AsanUbsan.M.loaded_segments (0x1c065c : word) = Some W_1c568c.
Proof. vm_refl. Qed.
Lemma D_1c568c : decode_any W_1c568c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c5690 : bv 32 := 0x0041e297.
Lemma F_1c5690 : fetch_word AsanUbsan.M.loaded_segments (0x1c0660 : word) = Some W_1c5690.
Proof. vm_refl. Qed.
Lemma D_1c5690 : decode_any W_1c5690 = Some (Auipc 5 1054, 4%Z).
Proof. vm_refl. Qed.
