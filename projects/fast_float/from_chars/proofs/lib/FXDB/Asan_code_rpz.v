(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_639d4 : bv 32 := 0xfc010113.
Lemma F_639d4 : fetch_word AsanUbsan.M.loaded_segments (0x639d4 : word) = Some W_639d4.
Proof. vm_refl. Qed.
Lemma D_639d4 : decode_any W_639d4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639d8 : bv 32 := 0x02113c23.
Lemma F_639d8 : fetch_word AsanUbsan.M.loaded_segments (0x639d8 : word) = Some W_639d8.
Proof. vm_refl. Qed.
Lemma D_639d8 : decode_any W_639d8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639dc : bv 32 := 0x02813823.
Lemma F_639dc : fetch_word AsanUbsan.M.loaded_segments (0x639dc : word) = Some W_639dc.
Proof. vm_refl. Qed.
Lemma D_639dc : decode_any W_639dc = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639e0 : bv 32 := 0x02913423.
Lemma F_639e0 : fetch_word AsanUbsan.M.loaded_segments (0x639e0 : word) = Some W_639e0.
Proof. vm_refl. Qed.
Lemma D_639e0 : decode_any W_639e0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639e4 : bv 32 := 0x03213023.
Lemma F_639e4 : fetch_word AsanUbsan.M.loaded_segments (0x639e4 : word) = Some W_639e4.
Proof. vm_refl. Qed.
Lemma D_639e4 : decode_any W_639e4 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639e8 : bv 32 := 0x01313c23.
Lemma F_639e8 : fetch_word AsanUbsan.M.loaded_segments (0x639e8 : word) = Some W_639e8.
Proof. vm_refl. Qed.
Lemma D_639e8 : decode_any W_639e8 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639ec : bv 32 := 0x01413823.
Lemma F_639ec : fetch_word AsanUbsan.M.loaded_segments (0x639ec : word) = Some W_639ec.
Proof. vm_refl. Qed.
Lemma D_639ec : decode_any W_639ec = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639f0 : bv 32 := 0x01513423.
Lemma F_639f0 : fetch_word AsanUbsan.M.loaded_segments (0x639f0 : word) = Some W_639f0.
Proof. vm_refl. Qed.
Lemma D_639f0 : decode_any W_639f0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639f4 : bv 32 := 0x14058c63.
Lemma F_639f4 : fetch_word AsanUbsan.M.loaded_segments (0x639f4 : word) = Some W_639f4.
Proof. vm_refl. Qed.
Lemma D_639f4 : decode_any W_639f4 = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639f8 : bv 32 := 0x00058493.
Lemma F_639f8 : fetch_word AsanUbsan.M.loaded_segments (0x639f8 : word) = Some W_639f8.
Proof. vm_refl. Qed.
Lemma D_639f8 : decode_any W_639f8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_639fc : bv 32 := 0x00050413.
Lemma F_639fc : fetch_word AsanUbsan.M.loaded_segments (0x639fc : word) = Some W_639fc.
Proof. vm_refl. Qed.
Lemma D_639fc : decode_any W_639fc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a00 : bv 32 := 0x0007b517.
Lemma F_63a00 : fetch_word AsanUbsan.M.loaded_segments (0x63a00 : word) = Some W_63a00.
Proof. vm_refl. Qed.
Lemma D_63a00 : decode_any W_63a00 = Some (Auipc 10 123, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a04 : bv 32 := 0xa9053a83.
Lemma F_63a04 : fetch_word AsanUbsan.M.loaded_segments (0x63a04 : word) = Some W_63a04.
Proof. vm_refl. Qed.
Lemma D_63a04 : decode_any W_63a04 = Some (Load SZ8 true 21 10 2704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a08 : bv 32 := 0x000ab583.
Lemma F_63a08 : fetch_word AsanUbsan.M.loaded_segments (0x63a08 : word) = Some W_63a08.
Proof. vm_refl. Qed.
Lemma D_63a08 : decode_any W_63a08 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a0c : bv 32 := 0xfff58513.
Lemma F_63a0c : fetch_word AsanUbsan.M.loaded_segments (0x63a0c : word) = Some W_63a0c.
Proof. vm_refl. Qed.
Lemma D_63a0c : decode_any W_63a0c = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a10 : bv 32 := 0x00a5b633.
Lemma F_63a10 : fetch_word AsanUbsan.M.loaded_segments (0x63a10 : word) = Some W_63a10.
Proof. vm_refl. Qed.
Lemma D_63a10 : decode_any W_63a10 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a14 : bv 32 := 0xfff60613.
Lemma F_63a14 : fetch_word AsanUbsan.M.loaded_segments (0x63a14 : word) = Some W_63a14.
Proof. vm_refl. Qed.
Lemma D_63a14 : decode_any W_63a14 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a18 : bv 32 := 0x00a67633.
Lemma F_63a18 : fetch_word AsanUbsan.M.loaded_segments (0x63a18 : word) = Some W_63a18.
Proof. vm_refl. Qed.
Lemma D_63a18 : decode_any W_63a18 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a1c : bv 32 := 0x04867263.
Lemma F_63a1c : fetch_word AsanUbsan.M.loaded_segments (0x63a1c : word) = Some W_63a1c.
Proof. vm_refl. Qed.
Lemma D_63a1c : decode_any W_63a1c = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a20 : bv 32 := 0x0007b697.
Lemma F_63a20 : fetch_word AsanUbsan.M.loaded_segments (0x63a20 : word) = Some W_63a20.
Proof. vm_refl. Qed.
Lemma D_63a20 : decode_any W_63a20 = Some (Auipc 13 123, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a24 : bv 32 := 0xa786b683.
Lemma F_63a24 : fetch_word AsanUbsan.M.loaded_segments (0x63a24 : word) = Some W_63a24.
Proof. vm_refl. Qed.
Lemma D_63a24 : decode_any W_63a24 = Some (Load SZ8 true 13 13 2680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a28 : bv 32 := 0x0007b717.
Lemma F_63a28 : fetch_word AsanUbsan.M.loaded_segments (0x63a28 : word) = Some W_63a28.
Proof. vm_refl. Qed.
Lemma D_63a28 : decode_any W_63a28 = Some (Auipc 14 123, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a2c : bv 32 := 0xa7873703.
Lemma F_63a2c : fetch_word AsanUbsan.M.loaded_segments (0x63a2c : word) = Some W_63a2c.
Proof. vm_refl. Qed.
Lemma D_63a2c : decode_any W_63a2c = Some (Load SZ8 true 14 14 2680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a30 : bv 32 := 0x0006b803.
Lemma F_63a30 : fetch_word AsanUbsan.M.loaded_segments (0x63a30 : word) = Some W_63a30.
Proof. vm_refl. Qed.
Lemma D_63a30 : decode_any W_63a30 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a34 : bv 32 := 0x00073683.
Lemma F_63a34 : fetch_word AsanUbsan.M.loaded_segments (0x63a34 : word) = Some W_63a34.
Proof. vm_refl. Qed.
Lemma D_63a34 : decode_any W_63a34 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a38 : bv 32 := 0xfff80793.
Lemma F_63a38 : fetch_word AsanUbsan.M.loaded_segments (0x63a38 : word) = Some W_63a38.
Proof. vm_refl. Qed.
Lemma D_63a38 : decode_any W_63a38 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a3c : bv 32 := 0x0087f463.
Lemma F_63a3c : fetch_word AsanUbsan.M.loaded_segments (0x63a3c : word) = Some W_63a3c.
Proof. vm_refl. Qed.
Lemma D_63a3c : decode_any W_63a3c = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a40 : bv 32 := 0x0286f063.
Lemma F_63a40 : fetch_word AsanUbsan.M.loaded_segments (0x63a40 : word) = Some W_63a40.
Proof. vm_refl. Qed.
Lemma D_63a40 : decode_any W_63a40 = Some (Branch BC_GEU 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a44 : bv 32 := 0x0007b717.
Lemma F_63a44 : fetch_word AsanUbsan.M.loaded_segments (0x63a44 : word) = Some W_63a44.
Proof. vm_refl. Qed.
Lemma D_63a44 : decode_any W_63a44 = Some (Auipc 14 123, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a48 : bv 32 := 0xa6473703.
Lemma F_63a48 : fetch_word AsanUbsan.M.loaded_segments (0x63a48 : word) = Some W_63a48.
Proof. vm_refl. Qed.
Lemma D_63a48 : decode_any W_63a48 = Some (Load SZ8 true 14 14 2660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a4c : bv 32 := 0x00073283.
Lemma F_63a4c : fetch_word AsanUbsan.M.loaded_segments (0x63a4c : word) = Some W_63a4c.
Proof. vm_refl. Qed.
Lemma D_63a4c : decode_any W_63a4c = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a50 : bv 32 := 0x0032d713.
Lemma F_63a50 : fetch_word AsanUbsan.M.loaded_segments (0x63a50 : word) = Some W_63a50.
Proof. vm_refl. Qed.
Lemma D_63a50 : decode_any W_63a50 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a54 : bv 32 := 0x00b708b3.
Lemma F_63a54 : fetch_word AsanUbsan.M.loaded_segments (0x63a54 : word) = Some W_63a54.
Proof. vm_refl. Qed.
Lemma D_63a54 : decode_any W_63a54 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a58 : bv 32 := 0x1282e063.
Lemma F_63a58 : fetch_word AsanUbsan.M.loaded_segments (0x63a58 : word) = Some W_63a58.
Proof. vm_refl. Qed.
Lemma D_63a58 : decode_any W_63a58 = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a5c : bv 32 := 0x1088fe63.
Lemma F_63a5c : fetch_word AsanUbsan.M.loaded_segments (0x63a5c : word) = Some W_63a5c.
Proof. vm_refl. Qed.
Lemma D_63a5c : decode_any W_63a5c = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a60 : bv 32 := 0x00848933.
Lemma F_63a60 : fetch_word AsanUbsan.M.loaded_segments (0x63a60 : word) = Some W_63a60.
Proof. vm_refl. Qed.
Lemma D_63a60 : decode_any W_63a60 = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a64 : bv 32 := 0x05267263.
Lemma F_63a64 : fetch_word AsanUbsan.M.loaded_segments (0x63a64 : word) = Some W_63a64.
Proof. vm_refl. Qed.
Lemma D_63a64 : decode_any W_63a64 = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a68 : bv 32 := 0x0007b617.
Lemma F_63a68 : fetch_word AsanUbsan.M.loaded_segments (0x63a68 : word) = Some W_63a68.
Proof. vm_refl. Qed.
Lemma D_63a68 : decode_any W_63a68 = Some (Auipc 12 123, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a6c : bv 32 := 0xa3063603.
Lemma F_63a6c : fetch_word AsanUbsan.M.loaded_segments (0x63a6c : word) = Some W_63a6c.
Proof. vm_refl. Qed.
Lemma D_63a6c : decode_any W_63a6c = Some (Load SZ8 true 12 12 2608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a70 : bv 32 := 0x0007b697.
Lemma F_63a70 : fetch_word AsanUbsan.M.loaded_segments (0x63a70 : word) = Some W_63a70.
Proof. vm_refl. Qed.
Lemma D_63a70 : decode_any W_63a70 = Some (Auipc 13 123, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a74 : bv 32 := 0xa306b683.
Lemma F_63a74 : fetch_word AsanUbsan.M.loaded_segments (0x63a74 : word) = Some W_63a74.
Proof. vm_refl. Qed.
Lemma D_63a74 : decode_any W_63a74 = Some (Load SZ8 true 13 13 2608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a78 : bv 32 := 0x00063783.
Lemma F_63a78 : fetch_word AsanUbsan.M.loaded_segments (0x63a78 : word) = Some W_63a78.
Proof. vm_refl. Qed.
Lemma D_63a78 : decode_any W_63a78 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a7c : bv 32 := 0x0006b603.
Lemma F_63a7c : fetch_word AsanUbsan.M.loaded_segments (0x63a7c : word) = Some W_63a7c.
Proof. vm_refl. Qed.
Lemma D_63a7c : decode_any W_63a7c = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a80 : bv 32 := 0xfff78713.
Lemma F_63a80 : fetch_word AsanUbsan.M.loaded_segments (0x63a80 : word) = Some W_63a80.
Proof. vm_refl. Qed.
Lemma D_63a80 : decode_any W_63a80 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a84 : bv 32 := 0x01277463.
Lemma F_63a84 : fetch_word AsanUbsan.M.loaded_segments (0x63a84 : word) = Some W_63a84.
Proof. vm_refl. Qed.
Lemma D_63a84 : decode_any W_63a84 = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a88 : bv 32 := 0x03267063.
Lemma F_63a88 : fetch_word AsanUbsan.M.loaded_segments (0x63a88 : word) = Some W_63a88.
Proof. vm_refl. Qed.
Lemma D_63a88 : decode_any W_63a88 = Some (Branch BC_GEU 12 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a8c : bv 32 := 0x0007b697.
Lemma F_63a8c : fetch_word AsanUbsan.M.loaded_segments (0x63a8c : word) = Some W_63a8c.
Proof. vm_refl. Qed.
Lemma D_63a8c : decode_any W_63a8c = Some (Auipc 13 123, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a90 : bv 32 := 0xa1c6b683.
Lemma F_63a90 : fetch_word AsanUbsan.M.loaded_segments (0x63a90 : word) = Some W_63a90.
Proof. vm_refl. Qed.
Lemma D_63a90 : decode_any W_63a90 = Some (Load SZ8 true 13 13 2588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a94 : bv 32 := 0x0006b883.
Lemma F_63a94 : fetch_word AsanUbsan.M.loaded_segments (0x63a94 : word) = Some W_63a94.
Proof. vm_refl. Qed.
Lemma D_63a94 : decode_any W_63a94 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a98 : bv 32 := 0x0038d693.
Lemma F_63a98 : fetch_word AsanUbsan.M.loaded_segments (0x63a98 : word) = Some W_63a98.
Proof. vm_refl. Qed.
Lemma D_63a98 : decode_any W_63a98 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63a9c : bv 32 := 0x00b68833.
Lemma F_63a9c : fetch_word AsanUbsan.M.loaded_segments (0x63a9c : word) = Some W_63a9c.
Proof. vm_refl. Qed.
Lemma D_63a9c : decode_any W_63a9c = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63aa0 : bv 32 := 0x1328e463.
Lemma F_63aa0 : fetch_word AsanUbsan.M.loaded_segments (0x63aa0 : word) = Some W_63aa0.
Proof. vm_refl. Qed.
Lemma D_63aa0 : decode_any W_63aa0 = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63aa4 : bv 32 := 0x13287263.
Lemma F_63aa4 : fetch_word AsanUbsan.M.loaded_segments (0x63aa4 : word) = Some W_63aa4.
Proof. vm_refl. Qed.
Lemma D_63aa4 : decode_any W_63aa4 = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63aa8 : bv 32 := 0x23247863.
Lemma F_63aa8 : fetch_word AsanUbsan.M.loaded_segments (0x63aa8 : word) = Some W_63aa8.
Proof. vm_refl. Qed.
Lemma D_63aa8 : decode_any W_63aa8 = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63aac : bv 32 := 0x00740513.
Lemma F_63aac : fetch_word AsanUbsan.M.loaded_segments (0x63aac : word) = Some W_63aac.
Proof. vm_refl. Qed.
Lemma D_63aac : decode_any W_63aac = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ab0 : bv 32 := 0xff857513.
Lemma F_63ab0 : fetch_word AsanUbsan.M.loaded_segments (0x63ab0 : word) = Some W_63ab0.
Proof. vm_refl. Qed.
Lemma D_63ab0 : decode_any W_63ab0 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ab4 : bv 32 := 0xff897a13.
Lemma F_63ab4 : fetch_word AsanUbsan.M.loaded_segments (0x63ab4 : word) = Some W_63ab4.
Proof. vm_refl. Qed.
Lemma D_63ab4 : decode_any W_63ab4 = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ab8 : bv 32 := 0xa91ff0ef.
Lemma F_63ab8 : fetch_word AsanUbsan.M.loaded_segments (0x63ab8 : word) = Some W_63ab8.
Proof. vm_refl. Qed.
Lemma D_63ab8 : decode_any W_63ab8 = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63abc : bv 32 := 0x00050993.
Lemma F_63abc : fetch_word AsanUbsan.M.loaded_segments (0x63abc : word) = Some W_63abc.
Proof. vm_refl. Qed.
Lemma D_63abc : decode_any W_63abc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ac0 : bv 32 := 0x000a0513.
Lemma F_63ac0 : fetch_word AsanUbsan.M.loaded_segments (0x63ac0 : word) = Some W_63ac0.
Proof. vm_refl. Qed.
Lemma D_63ac0 : decode_any W_63ac0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ac4 : bv 32 := 0xa85ff0ef.
Lemma F_63ac4 : fetch_word AsanUbsan.M.loaded_segments (0x63ac4 : word) = Some W_63ac4.
Proof. vm_refl. Qed.
Lemma D_63ac4 : decode_any W_63ac4 = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ac8 : bv 32 := 0x000ab583.
Lemma F_63ac8 : fetch_word AsanUbsan.M.loaded_segments (0x63ac8 : word) = Some W_63ac8.
Proof. vm_refl. Qed.
Lemma D_63ac8 : decode_any W_63ac8 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63acc : bv 32 := 0x00345613.
Lemma F_63acc : fetch_word AsanUbsan.M.loaded_segments (0x63acc : word) = Some W_63acc.
Proof. vm_refl. Qed.
Lemma D_63acc : decode_any W_63acc = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ad0 : bv 32 := 0x00c58633.
Lemma F_63ad0 : fetch_word AsanUbsan.M.loaded_segments (0x63ad0 : word) = Some W_63ad0.
Proof. vm_refl. Qed.
Lemma D_63ad0 : decode_any W_63ad0 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ad4 : bv 32 := 0x00060603.
Lemma F_63ad4 : fetch_word AsanUbsan.M.loaded_segments (0x63ad4 : word) = Some W_63ad4.
Proof. vm_refl. Qed.
Lemma D_63ad4 : decode_any W_63ad4 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ad8 : bv 32 := 0x00060663.
Lemma F_63ad8 : fetch_word AsanUbsan.M.loaded_segments (0x63ad8 : word) = Some W_63ad8.
Proof. vm_refl. Qed.
Lemma D_63ad8 : decode_any W_63ad8 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63adc : bv 32 := 0x00747693.
Lemma F_63adc : fetch_word AsanUbsan.M.loaded_segments (0x63adc : word) = Some W_63adc.
Proof. vm_refl. Qed.
Lemma D_63adc : decode_any W_63adc = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ae0 : bv 32 := 0x02c6d063.
Lemma F_63ae0 : fetch_word AsanUbsan.M.loaded_segments (0x63ae0 : word) = Some W_63ae0.
Proof. vm_refl. Qed.
Lemma D_63ae0 : decode_any W_63ae0 = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ae4 : bv 32 := 0xfff90913.
Lemma F_63ae4 : fetch_word AsanUbsan.M.loaded_segments (0x63ae4 : word) = Some W_63ae4.
Proof. vm_refl. Qed.
Lemma D_63ae4 : decode_any W_63ae4 = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63ae8 : bv 32 := 0x00395613.
Lemma F_63ae8 : fetch_word AsanUbsan.M.loaded_segments (0x63ae8 : word) = Some W_63ae8.
Proof. vm_refl. Qed.
Lemma D_63ae8 : decode_any W_63ae8 = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63aec : bv 32 := 0x00c585b3.
Lemma F_63aec : fetch_word AsanUbsan.M.loaded_segments (0x63aec : word) = Some W_63aec.
Proof. vm_refl. Qed.
Lemma D_63aec : decode_any W_63aec = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63af0 : bv 32 := 0x00058583.
Lemma F_63af0 : fetch_word AsanUbsan.M.loaded_segments (0x63af0 : word) = Some W_63af0.
Proof. vm_refl. Qed.
Lemma D_63af0 : decode_any W_63af0 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63af4 : bv 32 := 0x04058263.
Lemma F_63af4 : fetch_word AsanUbsan.M.loaded_segments (0x63af4 : word) = Some W_63af4.
Proof. vm_refl. Qed.
Lemma D_63af4 : decode_any W_63af4 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63af8 : bv 32 := 0x00797613.
Lemma F_63af8 : fetch_word AsanUbsan.M.loaded_segments (0x63af8 : word) = Some W_63af8.
Proof. vm_refl. Qed.
Lemma D_63af8 : decode_any W_63af8 = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63afc : bv 32 := 0x02b64e63.
Lemma F_63afc : fetch_word AsanUbsan.M.loaded_segments (0x63afc : word) = Some W_63afc.
Proof. vm_refl. Qed.
Lemma D_63afc : decode_any W_63afc = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b00 : bv 32 := 0x000ab503.
Lemma F_63b00 : fetch_word AsanUbsan.M.loaded_segments (0x63b00 : word) = Some W_63b00.
Proof. vm_refl. Qed.
Lemma D_63b00 : decode_any W_63b00 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b04 : bv 32 := 0x00040593.
Lemma F_63b04 : fetch_word AsanUbsan.M.loaded_segments (0x63b04 : word) = Some W_63b04.
Proof. vm_refl. Qed.
Lemma D_63b04 : decode_any W_63b04 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b08 : bv 32 := 0x0140006f.
Lemma F_63b08 : fetch_word AsanUbsan.M.loaded_segments (0x63b08 : word) = Some W_63b08.
Proof. vm_refl. Qed.
Lemma D_63b08 : decode_any W_63b08 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b0c : bv 32 := 0x00140413.
Lemma F_63b0c : fetch_word AsanUbsan.M.loaded_segments (0x63b0c : word) = Some W_63b0c.
Proof. vm_refl. Qed.
Lemma D_63b0c : decode_any W_63b0c = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b10 : bv 32 := 0xfff48493.
Lemma F_63b10 : fetch_word AsanUbsan.M.loaded_segments (0x63b10 : word) = Some W_63b10.
Proof. vm_refl. Qed.
Lemma D_63b10 : decode_any W_63b10 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b14 : bv 32 := 0x00158593.
Lemma F_63b14 : fetch_word AsanUbsan.M.loaded_segments (0x63b14 : word) = Some W_63b14.
Proof. vm_refl. Qed.
Lemma D_63b14 : decode_any W_63b14 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b18 : bv 32 := 0x1e048063.
Lemma F_63b18 : fetch_word AsanUbsan.M.loaded_segments (0x63b18 : word) = Some W_63b18.
Proof. vm_refl. Qed.
Lemma D_63b18 : decode_any W_63b18 = Some (Branch BC_EQ 9 0 480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b1c : bv 32 := 0x00345613.
Lemma F_63b1c : fetch_word AsanUbsan.M.loaded_segments (0x63b1c : word) = Some W_63b1c.
Proof. vm_refl. Qed.
Lemma D_63b1c : decode_any W_63b1c = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b20 : bv 32 := 0x00c50633.
Lemma F_63b20 : fetch_word AsanUbsan.M.loaded_segments (0x63b20 : word) = Some W_63b20.
Proof. vm_refl. Qed.
Lemma D_63b20 : decode_any W_63b20 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b24 : bv 32 := 0x00060603.
Lemma F_63b24 : fetch_word AsanUbsan.M.loaded_segments (0x63b24 : word) = Some W_63b24.
Proof. vm_refl. Qed.
Lemma D_63b24 : decode_any W_63b24 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b28 : bv 32 := 0xfe0602e3.
Lemma F_63b28 : fetch_word AsanUbsan.M.loaded_segments (0x63b28 : word) = Some W_63b28.
Proof. vm_refl. Qed.
Lemma D_63b28 : decode_any W_63b28 = Some (Branch BC_EQ 12 0 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b2c : bv 32 := 0x0075f693.
Lemma F_63b2c : fetch_word AsanUbsan.M.loaded_segments (0x63b2c : word) = Some W_63b2c.
Proof. vm_refl. Qed.
Lemma D_63b2c : decode_any W_63b2c = Some (OpImm ALU_AND 13 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b30 : bv 32 := 0xfcc6cee3.
Lemma F_63b30 : fetch_word AsanUbsan.M.loaded_segments (0x63b30 : word) = Some W_63b30.
Proof. vm_refl. Qed.
Lemma D_63b30 : decode_any W_63b30 = Some (Branch BC_LT 13 12 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b34 : bv 32 := 0x01c0006f.
Lemma F_63b34 : fetch_word AsanUbsan.M.loaded_segments (0x63b34 : word) = Some W_63b34.
Proof. vm_refl. Qed.
Lemma D_63b34 : decode_any W_63b34 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b38 : bv 32 := 0x00a9fa63.
Lemma F_63b38 : fetch_word AsanUbsan.M.loaded_segments (0x63b38 : word) = Some W_63b38.
Proof. vm_refl. Qed.
Lemma D_63b38 : decode_any W_63b38 = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b3c : bv 32 := 0x413505b3.
Lemma F_63b3c : fetch_word AsanUbsan.M.loaded_segments (0x63b3c : word) = Some W_63b3c.
Proof. vm_refl. Qed.
Lemma D_63b3c : decode_any W_63b3c = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b40 : bv 32 := 0x00098513.
Lemma F_63b40 : fetch_word AsanUbsan.M.loaded_segments (0x63b40 : word) = Some W_63b40.
Proof. vm_refl. Qed.
Lemma D_63b40 : decode_any W_63b40 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b44 : bv 32 := 0x6210f0ef.
Lemma F_63b44 : fetch_word AsanUbsan.M.loaded_segments (0x63b44 : word) = Some W_63b44.
Proof. vm_refl. Qed.
Lemma D_63b44 : decode_any W_63b44 = Some (Jal 1 65056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b48 : bv 32 := 0xfa050ce3.
Lemma F_63b48 : fetch_word AsanUbsan.M.loaded_segments (0x63b48 : word) = Some W_63b48.
Proof. vm_refl. Qed.
Lemma D_63b48 : decode_any W_63b48 = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b4c : bv 32 := 0x00000413.
Lemma F_63b4c : fetch_word AsanUbsan.M.loaded_segments (0x63b4c : word) = Some W_63b4c.
Proof. vm_refl. Qed.
Lemma D_63b4c : decode_any W_63b4c = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b50 : bv 32 := 0x00040513.
Lemma F_63b50 : fetch_word AsanUbsan.M.loaded_segments (0x63b50 : word) = Some W_63b50.
Proof. vm_refl. Qed.
Lemma D_63b50 : decode_any W_63b50 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b54 : bv 32 := 0x03813083.
Lemma F_63b54 : fetch_word AsanUbsan.M.loaded_segments (0x63b54 : word) = Some W_63b54.
Proof. vm_refl. Qed.
Lemma D_63b54 : decode_any W_63b54 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b58 : bv 32 := 0x03013403.
Lemma F_63b58 : fetch_word AsanUbsan.M.loaded_segments (0x63b58 : word) = Some W_63b58.
Proof. vm_refl. Qed.
Lemma D_63b58 : decode_any W_63b58 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b5c : bv 32 := 0x02813483.
Lemma F_63b5c : fetch_word AsanUbsan.M.loaded_segments (0x63b5c : word) = Some W_63b5c.
Proof. vm_refl. Qed.
Lemma D_63b5c : decode_any W_63b5c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b60 : bv 32 := 0x02013903.
Lemma F_63b60 : fetch_word AsanUbsan.M.loaded_segments (0x63b60 : word) = Some W_63b60.
Proof. vm_refl. Qed.
Lemma D_63b60 : decode_any W_63b60 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b64 : bv 32 := 0x01813983.
Lemma F_63b64 : fetch_word AsanUbsan.M.loaded_segments (0x63b64 : word) = Some W_63b64.
Proof. vm_refl. Qed.
Lemma D_63b64 : decode_any W_63b64 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b68 : bv 32 := 0x01013a03.
Lemma F_63b68 : fetch_word AsanUbsan.M.loaded_segments (0x63b68 : word) = Some W_63b68.
Proof. vm_refl. Qed.
Lemma D_63b68 : decode_any W_63b68 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b6c : bv 32 := 0x00813a83.
Lemma F_63b6c : fetch_word AsanUbsan.M.loaded_segments (0x63b6c : word) = Some W_63b6c.
Proof. vm_refl. Qed.
Lemma D_63b6c : decode_any W_63b6c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b70 : bv 32 := 0x04010113.
Lemma F_63b70 : fetch_word AsanUbsan.M.loaded_segments (0x63b70 : word) = Some W_63b70.
Proof. vm_refl. Qed.
Lemma D_63b70 : decode_any W_63b70 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b74 : bv 32 := 0x00008067.
Lemma F_63b74 : fetch_word AsanUbsan.M.loaded_segments (0x63b74 : word) = Some W_63b74.
Proof. vm_refl. Qed.
Lemma D_63b74 : decode_any W_63b74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63b78 : bv 32 := 0x0007b297.
Lemma F_63b78 : fetch_word AsanUbsan.M.loaded_segments (0x63b78 : word) = Some W_63b78.
Proof. vm_refl. Qed.
Lemma D_63b78 : decode_any W_63b78 = Some (Auipc 5 123, 4%Z).
Proof. vm_refl. Qed.
