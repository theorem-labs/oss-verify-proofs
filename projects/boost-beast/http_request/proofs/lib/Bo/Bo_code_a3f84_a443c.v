(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a3f84 : bv 32 := 0xfff71517.
Lemma F_a3f84 : fetch_word AsanUbsan.M.loaded_segments (0xa3f84 : word) = Some W_a3f84.
Proof. vm_refl. Qed.
Lemma D_a3f84 : decode_any W_a3f84 = Some (Auipc 10 1048433, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f88 : bv 32 := 0xa4050513.
Lemma F_a3f88 : fetch_word AsanUbsan.M.loaded_segments (0xa3f88 : word) = Some W_a3f88.
Proof. vm_refl. Qed.
Lemma D_a3f88 : decode_any W_a3f88 = Some (OpImm ALU_ADD 10 10 2624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f8c : bv 32 := 0x00008067.
Lemma F_a3f8c : fetch_word AsanUbsan.M.loaded_segments (0xa3f8c : word) = Some W_a3f8c.
Proof. vm_refl. Qed.
Lemma D_a3f8c : decode_any W_a3f8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f90 : bv 32 := 0xfff7d517.
Lemma F_a3f90 : fetch_word AsanUbsan.M.loaded_segments (0xa3f90 : word) = Some W_a3f90.
Proof. vm_refl. Qed.
Lemma D_a3f90 : decode_any W_a3f90 = Some (Auipc 10 1048445, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f94 : bv 32 := 0xecf50513.
Lemma F_a3f94 : fetch_word AsanUbsan.M.loaded_segments (0xa3f94 : word) = Some W_a3f94.
Proof. vm_refl. Qed.
Lemma D_a3f94 : decode_any W_a3f94 = Some (OpImm ALU_ADD 10 10 3791, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f98 : bv 32 := 0x00008067.
Lemma F_a3f98 : fetch_word AsanUbsan.M.loaded_segments (0xa3f98 : word) = Some W_a3f98.
Proof. vm_refl. Qed.
Lemma D_a3f98 : decode_any W_a3f98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f9c : bv 32 := 0xfb010113.
Lemma F_a3f9c : fetch_word AsanUbsan.M.loaded_segments (0xa3f9c : word) = Some W_a3f9c.
Proof. vm_refl. Qed.
Lemma D_a3f9c : decode_any W_a3f9c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fa0 : bv 32 := 0x04113423.
Lemma F_a3fa0 : fetch_word AsanUbsan.M.loaded_segments (0xa3fa0 : word) = Some W_a3fa0.
Proof. vm_refl. Qed.
Lemma D_a3fa0 : decode_any W_a3fa0 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fa4 : bv 32 := 0x04813023.
Lemma F_a3fa4 : fetch_word AsanUbsan.M.loaded_segments (0xa3fa4 : word) = Some W_a3fa4.
Proof. vm_refl. Qed.
Lemma D_a3fa4 : decode_any W_a3fa4 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fa8 : bv 32 := 0x02913c23.
Lemma F_a3fa8 : fetch_word AsanUbsan.M.loaded_segments (0xa3fa8 : word) = Some W_a3fa8.
Proof. vm_refl. Qed.
Lemma D_a3fa8 : decode_any W_a3fa8 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fac : bv 32 := 0x03213823.
Lemma F_a3fac : fetch_word AsanUbsan.M.loaded_segments (0xa3fac : word) = Some W_a3fac.
Proof. vm_refl. Qed.
Lemma D_a3fac : decode_any W_a3fac = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fb0 : bv 32 := 0x03313423.
Lemma F_a3fb0 : fetch_word AsanUbsan.M.loaded_segments (0xa3fb0 : word) = Some W_a3fb0.
Proof. vm_refl. Qed.
Lemma D_a3fb0 : decode_any W_a3fb0 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fb4 : bv 32 := 0x03413023.
Lemma F_a3fb4 : fetch_word AsanUbsan.M.loaded_segments (0xa3fb4 : word) = Some W_a3fb4.
Proof. vm_refl. Qed.
Lemma D_a3fb4 : decode_any W_a3fb4 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fb8 : bv 32 := 0x01513c23.
Lemma F_a3fb8 : fetch_word AsanUbsan.M.loaded_segments (0xa3fb8 : word) = Some W_a3fb8.
Proof. vm_refl. Qed.
Lemma D_a3fb8 : decode_any W_a3fb8 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fbc : bv 32 := 0x01613823.
Lemma F_a3fbc : fetch_word AsanUbsan.M.loaded_segments (0xa3fbc : word) = Some W_a3fbc.
Proof. vm_refl. Qed.
Lemma D_a3fbc : decode_any W_a3fbc = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fc0 : bv 32 := 0x01713423.
Lemma F_a3fc0 : fetch_word AsanUbsan.M.loaded_segments (0xa3fc0 : word) = Some W_a3fc0.
Proof. vm_refl. Qed.
Lemma D_a3fc0 : decode_any W_a3fc0 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fc4 : bv 32 := 0x00200413.
Lemma F_a3fc4 : fetch_word AsanUbsan.M.loaded_segments (0xa3fc4 : word) = Some W_a3fc4.
Proof. vm_refl. Qed.
Lemma D_a3fc4 : decode_any W_a3fc4 = Some (OpImm ALU_ADD 8 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fc8 : bv 32 := 0x16851663.
Lemma F_a3fc8 : fetch_word AsanUbsan.M.loaded_segments (0xa3fc8 : word) = Some W_a3fc8.
Proof. vm_refl. Qed.
Lemma D_a3fc8 : decode_any W_a3fc8 = Some (Branch BC_NE 10 8 364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fcc : bv 32 := 0x0085b903.
Lemma F_a3fcc : fetch_word AsanUbsan.M.loaded_segments (0xa3fcc : word) = Some W_a3fcc.
Proof. vm_refl. Qed.
Lemma D_a3fcc : decode_any W_a3fcc = Some (Load SZ8 true 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fd0 : bv 32 := 0x00090513.
Lemma F_a3fd0 : fetch_word AsanUbsan.M.loaded_segments (0xa3fd0 : word) = Some W_a3fd0.
Proof. vm_refl. Qed.
Lemma D_a3fd0 : decode_any W_a3fd0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fd4 : bv 32 := 0x00000593.
Lemma F_a3fd4 : fetch_word AsanUbsan.M.loaded_segments (0xa3fd4 : word) = Some W_a3fd4.
Proof. vm_refl. Qed.
Lemma D_a3fd4 : decode_any W_a3fd4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fd8 : bv 32 := 0x0855f0ef.
Lemma F_a3fd8 : fetch_word AsanUbsan.M.loaded_segments (0xa3fd8 : word) = Some W_a3fd8.
Proof. vm_refl. Qed.
Lemma D_a3fd8 : decode_any W_a3fd8 = Some (Jal 1 391300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fdc : bv 32 := 0x24054863.
Lemma F_a3fdc : fetch_word AsanUbsan.M.loaded_segments (0xa3fdc : word) = Some W_a3fdc.
Proof. vm_refl. Qed.
Lemma D_a3fdc : decode_any W_a3fdc = Some (Branch BC_LT 10 0 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fe0 : bv 32 := 0x00050a13.
Lemma F_a3fe0 : fetch_word AsanUbsan.M.loaded_segments (0xa3fe0 : word) = Some W_a3fe0.
Proof. vm_refl. Qed.
Lemma D_a3fe0 : decode_any W_a3fe0 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fe4 : bv 32 := 0x00010537.
Lemma F_a3fe4 : fetch_word AsanUbsan.M.loaded_segments (0xa3fe4 : word) = Some W_a3fe4.
Proof. vm_refl. Qed.
Lemma D_a3fe4 : decode_any W_a3fe4 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fe8 : bv 32 := 0x00010ab7.
Lemma F_a3fe8 : fetch_word AsanUbsan.M.loaded_segments (0xa3fe8 : word) = Some W_a3fe8.
Proof. vm_refl. Qed.
Lemma D_a3fe8 : decode_any W_a3fe8 = Some (Lui 21 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fec : bv 32 := 0xd58d00ef.
Lemma F_a3fec : fetch_word AsanUbsan.M.loaded_segments (0xa3fec : word) = Some W_a3fec.
Proof. vm_refl. Qed.
Lemma D_a3fec : decode_any W_a3fec = Some (Jal 1 1901912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ff0 : bv 32 := 0x24050a63.
Lemma F_a3ff0 : fetch_word AsanUbsan.M.loaded_segments (0xa3ff0 : word) = Some W_a3ff0.
Proof. vm_refl. Qed.
Lemma D_a3ff0 : decode_any W_a3ff0 = Some (Branch BC_EQ 10 0 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ff4 : bv 32 := 0x00050b93.
Lemma F_a3ff4 : fetch_word AsanUbsan.M.loaded_segments (0xa3ff4 : word) = Some W_a3ff4.
Proof. vm_refl. Qed.
Lemma D_a3ff4 : decode_any W_a3ff4 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ff8 : bv 32 := 0x00000993.
Lemma F_a3ff8 : fetch_word AsanUbsan.M.loaded_segments (0xa3ff8 : word) = Some W_a3ff8.
Proof. vm_refl. Qed.
Lemma D_a3ff8 : decode_any W_a3ff8 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ffc : bv 32 := 0x005ac517.
Lemma F_a3ffc : fetch_word AsanUbsan.M.loaded_segments (0xa3ffc : word) = Some W_a3ffc.
Proof. vm_refl. Qed.
Lemma D_a3ffc : decode_any W_a3ffc = Some (Auipc 10 1452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4000 : bv 32 := 0xe1450b13.
Lemma F_a4000 : fetch_word AsanUbsan.M.loaded_segments (0xa4000 : word) = Some W_a4000.
Proof. vm_refl. Qed.
Lemma D_a4000 : decode_any W_a4000 = Some (OpImm ALU_ADD 22 10 3604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4004 : bv 32 := 0x03501263.
Lemma F_a4004 : fetch_word AsanUbsan.M.loaded_segments (0xa4004 : word) = Some W_a4004.
Proof. vm_refl. Qed.
Lemma D_a4004 : decode_any W_a4004 = Some (Branch BC_NE 0 21 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4008 : bv 32 := 0x0280006f.
Lemma F_a4008 : fetch_word AsanUbsan.M.loaded_segments (0xa4008 : word) = Some W_a4008.
Proof. vm_refl. Qed.
Lemma D_a4008 : decode_any W_a4008 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a400c : bv 32 := 0x01348533.
Lemma F_a400c : fetch_word AsanUbsan.M.loaded_segments (0xa400c : word) = Some W_a400c.
Proof. vm_refl. Qed.
Lemma D_a400c : decode_any W_a400c = Some (Op ALU_ADD 10 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4010 : bv 32 := 0x000b0593.
Lemma F_a4010 : fetch_word AsanUbsan.M.loaded_segments (0xa4010 : word) = Some W_a4010.
Proof. vm_refl. Qed.
Lemma D_a4010 : decode_any W_a4010 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4014 : bv 32 := 0x000b8613.
Lemma F_a4014 : fetch_word AsanUbsan.M.loaded_segments (0xa4014 : word) = Some W_a4014.
Proof. vm_refl. Qed.
Lemma D_a4014 : decode_any W_a4014 = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4018 : bv 32 := 0x9a5ce0ef.
Lemma F_a4018 : fetch_word AsanUbsan.M.loaded_segments (0xa4018 : word) = Some W_a4018.
Proof. vm_refl. Qed.
Lemma D_a4018 : decode_any W_a4018 = Some (Jal 1 1894820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a401c : bv 32 := 0x013b89b3.
Lemma F_a401c : fetch_word AsanUbsan.M.loaded_segments (0xa401c : word) = Some W_a401c.
Proof. vm_refl. Qed.
Lemma D_a401c : decode_any W_a401c = Some (Op ALU_ADD 19 23 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4020 : bv 32 := 0x00048b93.
Lemma F_a4020 : fetch_word AsanUbsan.M.loaded_segments (0xa4020 : word) = Some W_a4020.
Proof. vm_refl. Qed.
Lemma D_a4020 : decode_any W_a4020 = Some (OpImm ALU_ADD 23 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4024 : bv 32 := 0x01598663.
Lemma F_a4024 : fetch_word AsanUbsan.M.loaded_segments (0xa4024 : word) = Some W_a4024.
Proof. vm_refl. Qed.
Lemma D_a4024 : decode_any W_a4024 = Some (Branch BC_EQ 19 21 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4028 : bv 32 := 0x000b8493.
Lemma F_a4028 : fetch_word AsanUbsan.M.loaded_segments (0xa4028 : word) = Some W_a4028.
Proof. vm_refl. Qed.
Lemma D_a4028 : decode_any W_a4028 = Some (OpImm ALU_ADD 9 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a402c : bv 32 := 0x03c0006f.
Lemma F_a402c : fetch_word AsanUbsan.M.loaded_segments (0xa402c : word) = Some W_a402c.
Proof. vm_refl. Qed.
Lemma D_a402c : decode_any W_a402c = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4030 : bv 32 := 0x01a9d513.
Lemma F_a4030 : fetch_word AsanUbsan.M.loaded_segments (0xa4030 : word) = Some W_a4030.
Proof. vm_refl. Qed.
Lemma D_a4030 : decode_any W_a4030 = Some (ShiftImm ALU_SRL 10 19 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4034 : bv 32 := 0x1a051863.
Lemma F_a4034 : fetch_word AsanUbsan.M.loaded_segments (0xa4034 : word) = Some W_a4034.
Proof. vm_refl. Qed.
Lemma D_a4034 : decode_any W_a4034 = Some (Branch BC_NE 10 0 432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4038 : bv 32 := 0x00199a93.
Lemma F_a4038 : fetch_word AsanUbsan.M.loaded_segments (0xa4038 : word) = Some W_a4038.
Proof. vm_refl. Qed.
Lemma D_a4038 : decode_any W_a4038 = Some (ShiftImm ALU_SLL 21 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a403c : bv 32 := 0x000a8513.
Lemma F_a403c : fetch_word AsanUbsan.M.loaded_segments (0xa403c : word) = Some W_a403c.
Proof. vm_refl. Qed.
Lemma D_a403c : decode_any W_a403c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4040 : bv 32 := 0xd04d00ef.
Lemma F_a4040 : fetch_word AsanUbsan.M.loaded_segments (0xa4040 : word) = Some W_a4040.
Proof. vm_refl. Qed.
Lemma D_a4040 : decode_any W_a4040 = Some (Jal 1 1901828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4044 : bv 32 := 0x1c050063.
Lemma F_a4044 : fetch_word AsanUbsan.M.loaded_segments (0xa4044 : word) = Some W_a4044.
Proof. vm_refl. Qed.
Lemma D_a4044 : decode_any W_a4044 = Some (Branch BC_EQ 10 0 448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4048 : bv 32 := 0x00050493.
Lemma F_a4048 : fetch_word AsanUbsan.M.loaded_segments (0xa4048 : word) = Some W_a4048.
Proof. vm_refl. Qed.
Lemma D_a4048 : decode_any W_a4048 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a404c : bv 32 := 0x00098a63.
Lemma F_a404c : fetch_word AsanUbsan.M.loaded_segments (0xa404c : word) = Some W_a404c.
Proof. vm_refl. Qed.
Lemma D_a404c : decode_any W_a404c = Some (Branch BC_EQ 19 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4050 : bv 32 := 0x00048513.
Lemma F_a4050 : fetch_word AsanUbsan.M.loaded_segments (0xa4050 : word) = Some W_a4050.
Proof. vm_refl. Qed.
Lemma D_a4050 : decode_any W_a4050 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4054 : bv 32 := 0x000b8593.
Lemma F_a4054 : fetch_word AsanUbsan.M.loaded_segments (0xa4054 : word) = Some W_a4054.
Proof. vm_refl. Qed.
Lemma D_a4054 : decode_any W_a4054 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4058 : bv 32 := 0x00098613.
Lemma F_a4058 : fetch_word AsanUbsan.M.loaded_segments (0xa4058 : word) = Some W_a4058.
Proof. vm_refl. Qed.
Lemma D_a4058 : decode_any W_a4058 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a405c : bv 32 := 0x961ce0ef.
Lemma F_a405c : fetch_word AsanUbsan.M.loaded_segments (0xa405c : word) = Some W_a405c.
Proof. vm_refl. Qed.
Lemma D_a405c : decode_any W_a405c = Some (Jal 1 1894752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4060 : bv 32 := 0x000b8513.
Lemma F_a4060 : fetch_word AsanUbsan.M.loaded_segments (0xa4060 : word) = Some W_a4060.
Proof. vm_refl. Qed.
Lemma D_a4060 : decode_any W_a4060 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4064 : bv 32 := 0xcdcd00ef.
Lemma F_a4064 : fetch_word AsanUbsan.M.loaded_segments (0xa4064 : word) = Some W_a4064.
Proof. vm_refl. Qed.
Lemma D_a4064 : decode_any W_a4064 = Some (Jal 1 1901788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4068 : bv 32 := 0x413a8633.
Lemma F_a4068 : fetch_word AsanUbsan.M.loaded_segments (0xa4068 : word) = Some W_a4068.
Proof. vm_refl. Qed.
Lemma D_a4068 : decode_any W_a4068 = Some (Op ALU_SUB 12 21 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a406c : bv 32 := 0x00010537.
Lemma F_a406c : fetch_word AsanUbsan.M.loaded_segments (0xa406c : word) = Some W_a406c.
Proof. vm_refl. Qed.
Lemma D_a406c : decode_any W_a406c = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4070 : bv 32 := 0x00a66463.
Lemma F_a4070 : fetch_word AsanUbsan.M.loaded_segments (0xa4070 : word) = Some W_a4070.
Proof. vm_refl. Qed.
Lemma D_a4070 : decode_any W_a4070 = Some (Branch BC_LTU 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4074 : bv 32 := 0x00010637.
Lemma F_a4074 : fetch_word AsanUbsan.M.loaded_segments (0xa4074 : word) = Some W_a4074.
Proof. vm_refl. Qed.
Lemma D_a4074 : decode_any W_a4074 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4078 : bv 32 := 0x000a0513.
Lemma F_a4078 : fetch_word AsanUbsan.M.loaded_segments (0xa4078 : word) = Some W_a4078.
Proof. vm_refl. Qed.
Lemma D_a4078 : decode_any W_a4078 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a407c : bv 32 := 0x000b0593.
Lemma F_a407c : fetch_word AsanUbsan.M.loaded_segments (0xa407c : word) = Some W_a407c.
Proof. vm_refl. Qed.
Lemma D_a407c : decode_any W_a407c = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4080 : bv 32 := 0xa3cbd0ef.
Lemma F_a4080 : fetch_word AsanUbsan.M.loaded_segments (0xa4080 : word) = Some W_a4080.
Proof. vm_refl. Qed.
Lemma D_a4080 : decode_any W_a4080 = Some (Jal 1 1823292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4084 : bv 32 := 0x14054263.
Lemma F_a4084 : fetch_word AsanUbsan.M.loaded_segments (0xa4084 : word) = Some W_a4084.
Proof. vm_refl. Qed.
Lemma D_a4084 : decode_any W_a4084 = Some (Branch BC_LT 10 0 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4088 : bv 32 := 0x00050b93.
Lemma F_a4088 : fetch_word AsanUbsan.M.loaded_segments (0xa4088 : word) = Some W_a4088.
Proof. vm_refl. Qed.
Lemma D_a4088 : decode_any W_a4088 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a408c : bv 32 := 0xf80510e3.
Lemma F_a408c : fetch_word AsanUbsan.M.loaded_segments (0xa408c : word) = Some W_a408c.
Proof. vm_refl. Qed.
Lemma D_a408c : decode_any W_a408c = Some (Branch BC_NE 10 0 8064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4090 : bv 32 := 0x000a0513.
Lemma F_a4090 : fetch_word AsanUbsan.M.loaded_segments (0xa4090 : word) = Some W_a4090.
Proof. vm_refl. Qed.
Lemma D_a4090 : decode_any W_a4090 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4094 : bv 32 := 0x538740ef.
Lemma F_a4094 : fetch_word AsanUbsan.M.loaded_segments (0xa4094 : word) = Some W_a4094.
Proof. vm_refl. Qed.
Lemma D_a4094 : decode_any W_a4094 = Some (Jal 1 476472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4098 : bv 32 := 0x00500513.
Lemma F_a4098 : fetch_word AsanUbsan.M.loaded_segments (0xa4098 : word) = Some W_a4098.
Proof. vm_refl. Qed.
Lemma D_a4098 : decode_any W_a4098 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a409c : bv 32 := 0x0b357c63.
Lemma F_a409c : fetch_word AsanUbsan.M.loaded_segments (0xa409c : word) = Some W_a409c.
Proof. vm_refl. Qed.
Lemma D_a409c : decode_any W_a409c = Some (Branch BC_GEU 10 19 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40a0 : bv 32 := 0x00148a83.
Lemma F_a40a0 : fetch_word AsanUbsan.M.loaded_segments (0xa40a0 : word) = Some W_a40a0.
Proof. vm_refl. Qed.
Lemma D_a40a0 : decode_any W_a40a0 = Some (Load SZ1 true 21 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40a4 : bv 32 := 0x0004c503.
Lemma F_a40a4 : fetch_word AsanUbsan.M.loaded_segments (0xa40a4 : word) = Some W_a40a4.
Proof. vm_refl. Qed.
Lemma D_a40a4 : decode_any W_a40a4 = Some (Load SZ1 false 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40a8 : bv 32 := 0x039a9593.
Lemma F_a40a8 : fetch_word AsanUbsan.M.loaded_segments (0xa40a8 : word) = Some W_a40a8.
Proof. vm_refl. Qed.
Lemma D_a40a8 : decode_any W_a40a8 = Some (ShiftImm ALU_SLL 11 21 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40ac : bv 32 := 0x0315d593.
Lemma F_a40ac : fetch_word AsanUbsan.M.loaded_segments (0xa40ac : word) = Some W_a40ac.
Proof. vm_refl. Qed.
Lemma D_a40ac : decode_any W_a40ac = Some (ShiftImm ALU_SRL 11 11 49, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40b0 : bv 32 := 0x00a5e933.
Lemma F_a40b0 : fetch_word AsanUbsan.M.loaded_segments (0xa40b0 : word) = Some W_a40b0.
Proof. vm_refl. Qed.
Lemma D_a40b0 : decode_any W_a40b0 = Some (Op ALU_OR 18 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40b4 : bv 32 := 0x00690513.
Lemma F_a40b4 : fetch_word AsanUbsan.M.loaded_segments (0xa40b4 : word) = Some W_a40b4.
Proof. vm_refl. Qed.
Lemma D_a40b4 : decode_any W_a40b4 = Some (OpImm ALU_ADD 10 18 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40b8 : bv 32 := 0x0aa9ec63.
Lemma F_a40b8 : fetch_word AsanUbsan.M.loaded_segments (0xa40b8 : word) = Some W_a40b8.
Proof. vm_refl. Qed.
Lemma D_a40b8 : decode_any W_a40b8 = Some (Branch BC_LTU 19 10 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40bc : bv 32 := 0x00248413.
Lemma F_a40bc : fetch_word AsanUbsan.M.loaded_segments (0xa40bc : word) = Some W_a40bc.
Proof. vm_refl. Qed.
Lemma D_a40bc : decode_any W_a40bc = Some (OpImm ALU_ADD 8 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40c0 : bv 32 := 0x01240533.
Lemma F_a40c0 : fetch_word AsanUbsan.M.loaded_segments (0xa40c0 : word) = Some W_a40c0.
Proof. vm_refl. Qed.
Lemma D_a40c0 : decode_any W_a40c0 = Some (Op ALU_ADD 10 8 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40c4 : bv 32 := 0x00154583.
Lemma F_a40c4 : fetch_word AsanUbsan.M.loaded_segments (0xa40c4 : word) = Some W_a40c4.
Proof. vm_refl. Qed.
Lemma D_a40c4 : decode_any W_a40c4 = Some (Load SZ1 false 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40c8 : bv 32 := 0x00054603.
Lemma F_a40c8 : fetch_word AsanUbsan.M.loaded_segments (0xa40c8 : word) = Some W_a40c8.
Proof. vm_refl. Qed.
Lemma D_a40c8 : decode_any W_a40c8 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40cc : bv 32 := 0x00254683.
Lemma F_a40cc : fetch_word AsanUbsan.M.loaded_segments (0xa40cc : word) = Some W_a40cc.
Proof. vm_refl. Qed.
Lemma D_a40cc : decode_any W_a40cc = Some (Load SZ1 false 13 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40d0 : bv 32 := 0x00354703.
Lemma F_a40d0 : fetch_word AsanUbsan.M.loaded_segments (0xa40d0 : word) = Some W_a40d0.
Proof. vm_refl. Qed.
Lemma D_a40d0 : decode_any W_a40d0 = Some (Load SZ1 false 14 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40d4 : bv 32 := 0x00859593.
Lemma F_a40d4 : fetch_word AsanUbsan.M.loaded_segments (0xa40d4 : word) = Some W_a40d4.
Proof. vm_refl. Qed.
Lemma D_a40d4 : decode_any W_a40d4 = Some (ShiftImm ALU_SLL 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40d8 : bv 32 := 0x00c5e5b3.
Lemma F_a40d8 : fetch_word AsanUbsan.M.loaded_segments (0xa40d8 : word) = Some W_a40d8.
Proof. vm_refl. Qed.
Lemma D_a40d8 : decode_any W_a40d8 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40dc : bv 32 := 0x41298a33.
Lemma F_a40dc : fetch_word AsanUbsan.M.loaded_segments (0xa40dc : word) = Some W_a40dc.
Proof. vm_refl. Qed.
Lemma D_a40dc : decode_any W_a40dc = Some (Op ALU_SUB 20 19 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40e0 : bv 32 := 0x00450993.
Lemma F_a40e0 : fetch_word AsanUbsan.M.loaded_segments (0xa40e0 : word) = Some W_a40e0.
Proof. vm_refl. Qed.
Lemma D_a40e0 : decode_any W_a40e0 = Some (OpImm ALU_ADD 19 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40e4 : bv 32 := 0x01069693.
Lemma F_a40e4 : fetch_word AsanUbsan.M.loaded_segments (0xa40e4 : word) = Some W_a40e4.
Proof. vm_refl. Qed.
Lemma D_a40e4 : decode_any W_a40e4 = Some (ShiftImm ALU_SLL 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40e8 : bv 32 := 0x0187151b.
Lemma F_a40e8 : fetch_word AsanUbsan.M.loaded_segments (0xa40e8 : word) = Some W_a40e8.
Proof. vm_refl. Qed.
Lemma D_a40e8 : decode_any W_a40e8 = Some (ShiftImm32 ALU_SLL 10 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40ec : bv 32 := 0x00a6e533.
Lemma F_a40ec : fetch_word AsanUbsan.M.loaded_segments (0xa40ec : word) = Some W_a40ec.
Proof. vm_refl. Qed.
Lemma D_a40ec : decode_any W_a40ec = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40f0 : bv 32 := 0x00a5e533.
Lemma F_a40f0 : fetch_word AsanUbsan.M.loaded_segments (0xa40f0 : word) = Some W_a40f0.
Proof. vm_refl. Qed.
Lemma D_a40f0 : decode_any W_a40f0 = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40f4 : bv 32 := 0xffaa0a13.
Lemma F_a40f4 : fetch_word AsanUbsan.M.loaded_segments (0xa40f4 : word) = Some W_a40f4.
Proof. vm_refl. Qed.
Lemma D_a40f4 : decode_any W_a40f4 = Some (OpImm ALU_ADD 20 20 4090, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40f8 : bv 32 := 0x168000ef.
Lemma F_a40f8 : fetch_word AsanUbsan.M.loaded_segments (0xa40f8 : word) = Some W_a40f8.
Proof. vm_refl. Qed.
Lemma D_a40f8 : decode_any W_a40f8 = Some (Jal 1 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40fc : bv 32 := 0x00040513.
Lemma F_a40fc : fetch_word AsanUbsan.M.loaded_segments (0xa40fc : word) = Some W_a40fc.
Proof. vm_refl. Qed.
Lemma D_a40fc : decode_any W_a40fc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4100 : bv 32 := 0x00090593.
Lemma F_a4100 : fetch_word AsanUbsan.M.loaded_segments (0xa4100 : word) = Some W_a4100.
Proof. vm_refl. Qed.
Lemma D_a4100 : decode_any W_a4100 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4104 : bv 32 := 0x00098613.
Lemma F_a4104 : fetch_word AsanUbsan.M.loaded_segments (0xa4104 : word) = Some W_a4104.
Proof. vm_refl. Qed.
Lemma D_a4104 : decode_any W_a4104 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4108 : bv 32 := 0x000a0693.
Lemma F_a4108 : fetch_word AsanUbsan.M.loaded_segments (0xa4108 : word) = Some W_a4108.
Proof. vm_refl. Qed.
Lemma D_a4108 : decode_any W_a4108 = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a410c : bv 32 := 0x160000ef.
Lemma F_a410c : fetch_word AsanUbsan.M.loaded_segments (0xa410c : word) = Some W_a410c.
Proof. vm_refl. Qed.
Lemma D_a410c : decode_any W_a410c = Some (Jal 1 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4110 : bv 32 := 0x000ac663.
Lemma F_a4110 : fetch_word AsanUbsan.M.loaded_segments (0xa4110 : word) = Some W_a4110.
Proof. vm_refl. Qed.
Lemma D_a4110 : decode_any W_a4110 = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4114 : bv 32 := 0x00050413.
Lemma F_a4114 : fetch_word AsanUbsan.M.loaded_segments (0xa4114 : word) = Some W_a4114.
Proof. vm_refl. Qed.
Lemma D_a4114 : decode_any W_a4114 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4118 : bv 32 := 0x0780006f.
Lemma F_a4118 : fetch_word AsanUbsan.M.loaded_segments (0xa4118 : word) = Some W_a4118.
Proof. vm_refl. Qed.
Lemma D_a4118 : decode_any W_a4118 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a411c : bv 32 := 0x148000ef.
Lemma F_a411c : fetch_word AsanUbsan.M.loaded_segments (0xa411c : word) = Some W_a411c.
Proof. vm_refl. Qed.
Lemma D_a411c : decode_any W_a411c = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4120 : bv 32 := 0x0fb00593.
Lemma F_a4120 : fetch_word AsanUbsan.M.loaded_segments (0xa4120 : word) = Some W_a4120.
Proof. vm_refl. Qed.
Lemma D_a4120 : decode_any W_a4120 = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4124 : bv 32 := 0x00050413.
Lemma F_a4124 : fetch_word AsanUbsan.M.loaded_segments (0xa4124 : word) = Some W_a4124.
Proof. vm_refl. Qed.
Lemma D_a4124 : decode_any W_a4124 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4128 : bv 32 := 0x06b56463.
Lemma F_a4128 : fetch_word AsanUbsan.M.loaded_segments (0xa4128 : word) = Some W_a4128.
Proof. vm_refl. Qed.
Lemma D_a4128 : decode_any W_a4128 = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a412c : bv 32 := 0x0fb00413.
Lemma F_a412c : fetch_word AsanUbsan.M.loaded_segments (0xa412c : word) = Some W_a412c.
Proof. vm_refl. Qed.
Lemma D_a412c : decode_any W_a412c = Some (OpImm ALU_ADD 8 0 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4130 : bv 32 := 0x0600006f.
Lemma F_a4130 : fetch_word AsanUbsan.M.loaded_segments (0xa4130 : word) = Some W_a4130.
Proof. vm_refl. Qed.
Lemma D_a4130 : decode_any W_a4130 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4134 : bv 32 := 0x0007c517.
Lemma F_a4134 : fetch_word AsanUbsan.M.loaded_segments (0xa4134 : word) = Some W_a4134.
Proof. vm_refl. Qed.
Lemma D_a4134 : decode_any W_a4134 = Some (Auipc 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4138 : bv 32 := 0x1b453503.
Lemma F_a4138 : fetch_word AsanUbsan.M.loaded_segments (0xa4138 : word) = Some W_a4138.
Proof. vm_refl. Qed.
Lemma D_a4138 : decode_any W_a4138 = Some (Load SZ8 true 10 10 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a413c : bv 32 := 0x00053503.
Lemma F_a413c : fetch_word AsanUbsan.M.loaded_segments (0xa413c : word) = Some W_a413c.
Proof. vm_refl. Qed.
Lemma D_a413c : decode_any W_a413c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4140 : bv 32 := 0x0005b603.
Lemma F_a4140 : fetch_word AsanUbsan.M.loaded_segments (0xa4140 : word) = Some W_a4140.
Proof. vm_refl. Qed.
Lemma D_a4140 : decode_any W_a4140 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4144 : bv 32 := 0xfff72597.
Lemma F_a4144 : fetch_word AsanUbsan.M.loaded_segments (0xa4144 : word) = Some W_a4144.
Proof. vm_refl. Qed.
Lemma D_a4144 : decode_any W_a4144 = Some (Auipc 11 1048434, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4148 : bv 32 := 0x6ce58593.
Lemma F_a4148 : fetch_word AsanUbsan.M.loaded_segments (0xa4148 : word) = Some W_a4148.
Proof. vm_refl. Qed.
Lemma D_a4148 : decode_any W_a4148 = Some (OpImm ALU_ADD 11 11 1742, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a414c : bv 32 := 0x990bd0ef.
Lemma F_a414c : fetch_word AsanUbsan.M.loaded_segments (0xa414c : word) = Some W_a414c.
Proof. vm_refl. Qed.
Lemma D_a414c : decode_any W_a414c = Some (Jal 1 1823120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4150 : bv 32 := 0x0480006f.
Lemma F_a4150 : fetch_word AsanUbsan.M.loaded_segments (0xa4150 : word) = Some W_a4150.
Proof. vm_refl. Qed.
Lemma D_a4150 : decode_any W_a4150 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4154 : bv 32 := 0x0007c517.
Lemma F_a4154 : fetch_word AsanUbsan.M.loaded_segments (0xa4154 : word) = Some W_a4154.
Proof. vm_refl. Qed.
Lemma D_a4154 : decode_any W_a4154 = Some (Auipc 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4158 : bv 32 := 0x19453503.
Lemma F_a4158 : fetch_word AsanUbsan.M.loaded_segments (0xa4158 : word) = Some W_a4158.
Proof. vm_refl. Qed.
Lemma D_a4158 : decode_any W_a4158 = Some (Load SZ8 true 10 10 404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a415c : bv 32 := 0x00053683.
Lemma F_a415c : fetch_word AsanUbsan.M.loaded_segments (0xa415c : word) = Some W_a415c.
Proof. vm_refl. Qed.
Lemma D_a415c : decode_any W_a415c = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4160 : bv 32 := 0xfff7f517.
Lemma F_a4160 : fetch_word AsanUbsan.M.loaded_segments (0xa4160 : word) = Some W_a4160.
Proof. vm_refl. Qed.
Lemma D_a4160 : decode_any W_a4160 = Some (Auipc 10 1048447, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4164 : bv 32 := 0x01f00593.
Lemma F_a4164 : fetch_word AsanUbsan.M.loaded_segments (0xa4164 : word) = Some W_a4164.
Proof. vm_refl. Qed.
Lemma D_a4164 : decode_any W_a4164 = Some (OpImm ALU_ADD 11 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4168 : bv 32 := 0xfd150513.
Lemma F_a4168 : fetch_word AsanUbsan.M.loaded_segments (0xa4168 : word) = Some W_a4168.
Proof. vm_refl. Qed.
Lemma D_a4168 : decode_any W_a4168 = Some (OpImm ALU_ADD 10 10 4049, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a416c : bv 32 := 0x01c0006f.
Lemma F_a416c : fetch_word AsanUbsan.M.loaded_segments (0xa416c : word) = Some W_a416c.
Proof. vm_refl. Qed.
Lemma D_a416c : decode_any W_a416c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4170 : bv 32 := 0x0007c517.
Lemma F_a4170 : fetch_word AsanUbsan.M.loaded_segments (0xa4170 : word) = Some W_a4170.
Proof. vm_refl. Qed.
Lemma D_a4170 : decode_any W_a4170 = Some (Auipc 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4174 : bv 32 := 0x17853503.
Lemma F_a4174 : fetch_word AsanUbsan.M.loaded_segments (0xa4174 : word) = Some W_a4174.
Proof. vm_refl. Qed.
Lemma D_a4174 : decode_any W_a4174 = Some (Load SZ8 true 10 10 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4178 : bv 32 := 0x00053683.
Lemma F_a4178 : fetch_word AsanUbsan.M.loaded_segments (0xa4178 : word) = Some W_a4178.
Proof. vm_refl. Qed.
Lemma D_a4178 : decode_any W_a4178 = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a417c : bv 32 := 0xfff72517.
Lemma F_a417c : fetch_word AsanUbsan.M.loaded_segments (0xa417c : word) = Some W_a417c.
Proof. vm_refl. Qed.
Lemma D_a417c : decode_any W_a417c = Some (Auipc 10 1048434, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4180 : bv 32 := 0x01f00593.
Lemma F_a4180 : fetch_word AsanUbsan.M.loaded_segments (0xa4180 : word) = Some W_a4180.
Proof. vm_refl. Qed.
Lemma D_a4180 : decode_any W_a4180 = Some (OpImm ALU_ADD 11 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4184 : bv 32 := 0x6a750513.
Lemma F_a4184 : fetch_word AsanUbsan.M.loaded_segments (0xa4184 : word) = Some W_a4184.
Proof. vm_refl. Qed.
Lemma D_a4184 : decode_any W_a4184 = Some (OpImm ALU_ADD 10 10 1703, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4188 : bv 32 := 0x00100613.
Lemma F_a4188 : fetch_word AsanUbsan.M.loaded_segments (0xa4188 : word) = Some W_a4188.
Proof. vm_refl. Qed.
Lemma D_a4188 : decode_any W_a4188 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a418c : bv 32 := 0x938bd0ef.
Lemma F_a418c : fetch_word AsanUbsan.M.loaded_segments (0xa418c : word) = Some W_a418c.
Proof. vm_refl. Qed.
Lemma D_a418c : decode_any W_a418c = Some (Jal 1 1823032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4190 : bv 32 := 0x00048513.
Lemma F_a4190 : fetch_word AsanUbsan.M.loaded_segments (0xa4190 : word) = Some W_a4190.
Proof. vm_refl. Qed.
Lemma D_a4190 : decode_any W_a4190 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4194 : bv 32 := 0xbacd00ef.
Lemma F_a4194 : fetch_word AsanUbsan.M.loaded_segments (0xa4194 : word) = Some W_a4194.
Proof. vm_refl. Qed.
Lemma D_a4194 : decode_any W_a4194 = Some (Jal 1 1901484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4198 : bv 32 := 0x00040513.
Lemma F_a4198 : fetch_word AsanUbsan.M.loaded_segments (0xa4198 : word) = Some W_a4198.
Proof. vm_refl. Qed.
Lemma D_a4198 : decode_any W_a4198 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a419c : bv 32 := 0x04813083.
Lemma F_a419c : fetch_word AsanUbsan.M.loaded_segments (0xa419c : word) = Some W_a419c.
Proof. vm_refl. Qed.
Lemma D_a419c : decode_any W_a419c = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41a0 : bv 32 := 0x04013403.
Lemma F_a41a0 : fetch_word AsanUbsan.M.loaded_segments (0xa41a0 : word) = Some W_a41a0.
Proof. vm_refl. Qed.
Lemma D_a41a0 : decode_any W_a41a0 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41a4 : bv 32 := 0x03813483.
Lemma F_a41a4 : fetch_word AsanUbsan.M.loaded_segments (0xa41a4 : word) = Some W_a41a4.
Proof. vm_refl. Qed.
Lemma D_a41a4 : decode_any W_a41a4 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41a8 : bv 32 := 0x03013903.
Lemma F_a41a8 : fetch_word AsanUbsan.M.loaded_segments (0xa41a8 : word) = Some W_a41a8.
Proof. vm_refl. Qed.
Lemma D_a41a8 : decode_any W_a41a8 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41ac : bv 32 := 0x02813983.
Lemma F_a41ac : fetch_word AsanUbsan.M.loaded_segments (0xa41ac : word) = Some W_a41ac.
Proof. vm_refl. Qed.
Lemma D_a41ac : decode_any W_a41ac = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41b0 : bv 32 := 0x02013a03.
Lemma F_a41b0 : fetch_word AsanUbsan.M.loaded_segments (0xa41b0 : word) = Some W_a41b0.
Proof. vm_refl. Qed.
Lemma D_a41b0 : decode_any W_a41b0 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41b4 : bv 32 := 0x01813a83.
Lemma F_a41b4 : fetch_word AsanUbsan.M.loaded_segments (0xa41b4 : word) = Some W_a41b4.
Proof. vm_refl. Qed.
Lemma D_a41b4 : decode_any W_a41b4 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41b8 : bv 32 := 0x01013b03.
Lemma F_a41b8 : fetch_word AsanUbsan.M.loaded_segments (0xa41b8 : word) = Some W_a41b8.
Proof. vm_refl. Qed.
Lemma D_a41b8 : decode_any W_a41b8 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41bc : bv 32 := 0x00813b83.
Lemma F_a41bc : fetch_word AsanUbsan.M.loaded_segments (0xa41bc : word) = Some W_a41bc.
Proof. vm_refl. Qed.
Lemma D_a41bc : decode_any W_a41bc = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41c0 : bv 32 := 0x05010113.
Lemma F_a41c0 : fetch_word AsanUbsan.M.loaded_segments (0xa41c0 : word) = Some W_a41c0.
Proof. vm_refl. Qed.
Lemma D_a41c0 : decode_any W_a41c0 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41c4 : bv 32 := 0x00008067.
Lemma F_a41c4 : fetch_word AsanUbsan.M.loaded_segments (0xa41c4 : word) = Some W_a41c4.
Proof. vm_refl. Qed.
Lemma D_a41c4 : decode_any W_a41c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41c8 : bv 32 := 0x0007c517.
Lemma F_a41c8 : fetch_word AsanUbsan.M.loaded_segments (0xa41c8 : word) = Some W_a41c8.
Proof. vm_refl. Qed.
Lemma D_a41c8 : decode_any W_a41c8 = Some (Auipc 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41cc : bv 32 := 0x12053503.
Lemma F_a41cc : fetch_word AsanUbsan.M.loaded_segments (0xa41cc : word) = Some W_a41cc.
Proof. vm_refl. Qed.
Lemma D_a41cc : decode_any W_a41cc = Some (Load SZ8 true 10 10 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41d0 : bv 32 := 0x00053503.
Lemma F_a41d0 : fetch_word AsanUbsan.M.loaded_segments (0xa41d0 : word) = Some W_a41d0.
Proof. vm_refl. Qed.
Lemma D_a41d0 : decode_any W_a41d0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41d4 : bv 32 := 0xfff7c597.
Lemma F_a41d4 : fetch_word AsanUbsan.M.loaded_segments (0xa41d4 : word) = Some W_a41d4.
Proof. vm_refl. Qed.
Lemma D_a41d4 : decode_any W_a41d4 = Some (Auipc 11 1048444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41d8 : bv 32 := 0x37d58593.
Lemma F_a41d8 : fetch_word AsanUbsan.M.loaded_segments (0xa41d8 : word) = Some W_a41d8.
Proof. vm_refl. Qed.
Lemma D_a41d8 : decode_any W_a41d8 = Some (OpImm ALU_ADD 11 11 893, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41dc : bv 32 := 0x00090613.
Lemma F_a41dc : fetch_word AsanUbsan.M.loaded_segments (0xa41dc : word) = Some W_a41dc.
Proof. vm_refl. Qed.
Lemma D_a41dc : decode_any W_a41dc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41e0 : bv 32 := 0x01c0006f.
Lemma F_a41e0 : fetch_word AsanUbsan.M.loaded_segments (0xa41e0 : word) = Some W_a41e0.
Proof. vm_refl. Qed.
Lemma D_a41e0 : decode_any W_a41e0 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41e4 : bv 32 := 0x0007c517.
Lemma F_a41e4 : fetch_word AsanUbsan.M.loaded_segments (0xa41e4 : word) = Some W_a41e4.
Proof. vm_refl. Qed.
Lemma D_a41e4 : decode_any W_a41e4 = Some (Auipc 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41e8 : bv 32 := 0x10453503.
Lemma F_a41e8 : fetch_word AsanUbsan.M.loaded_segments (0xa41e8 : word) = Some W_a41e8.
Proof. vm_refl. Qed.
Lemma D_a41e8 : decode_any W_a41e8 = Some (Load SZ8 true 10 10 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41ec : bv 32 := 0x00053503.
Lemma F_a41ec : fetch_word AsanUbsan.M.loaded_segments (0xa41ec : word) = Some W_a41ec.
Proof. vm_refl. Qed.
Lemma D_a41ec : decode_any W_a41ec = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41f0 : bv 32 := 0xfff77597.
Lemma F_a41f0 : fetch_word AsanUbsan.M.loaded_segments (0xa41f0 : word) = Some W_a41f0.
Proof. vm_refl. Qed.
Lemma D_a41f0 : decode_any W_a41f0 = Some (Auipc 11 1048439, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41f4 : bv 32 := 0x54a58593.
Lemma F_a41f4 : fetch_word AsanUbsan.M.loaded_segments (0xa41f4 : word) = Some W_a41f4.
Proof. vm_refl. Qed.
Lemma D_a41f4 : decode_any W_a41f4 = Some (OpImm ALU_ADD 11 11 1354, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41f8 : bv 32 := 0x04000637.
Lemma F_a41f8 : fetch_word AsanUbsan.M.loaded_segments (0xa41f8 : word) = Some W_a41f8.
Proof. vm_refl. Qed.
Lemma D_a41f8 : decode_any W_a41f8 = Some (Lui 12 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a41fc : bv 32 := 0x8e0bd0ef.
Lemma F_a41fc : fetch_word AsanUbsan.M.loaded_segments (0xa41fc : word) = Some W_a41fc.
Proof. vm_refl. Qed.
Lemma D_a41fc : decode_any W_a41fc = Some (Jal 1 1822944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4200 : bv 32 := 0x0240006f.
Lemma F_a4200 : fetch_word AsanUbsan.M.loaded_segments (0xa4200 : word) = Some W_a4200.
Proof. vm_refl. Qed.
Lemma D_a4200 : decode_any W_a4200 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4204 : bv 32 := 0x0007c517.
Lemma F_a4204 : fetch_word AsanUbsan.M.loaded_segments (0xa4204 : word) = Some W_a4204.
Proof. vm_refl. Qed.
Lemma D_a4204 : decode_any W_a4204 = Some (Auipc 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4208 : bv 32 := 0x0e453503.
Lemma F_a4208 : fetch_word AsanUbsan.M.loaded_segments (0xa4208 : word) = Some W_a4208.
Proof. vm_refl. Qed.
Lemma D_a4208 : decode_any W_a4208 = Some (Load SZ8 true 10 10 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a420c : bv 32 := 0x00053683.
Lemma F_a420c : fetch_word AsanUbsan.M.loaded_segments (0xa420c : word) = Some W_a420c.
Proof. vm_refl. Qed.
Lemma D_a420c : decode_any W_a420c = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4210 : bv 32 := 0xfff71517.
Lemma F_a4210 : fetch_word AsanUbsan.M.loaded_segments (0xa4210 : word) = Some W_a4210.
Proof. vm_refl. Qed.
Lemma D_a4210 : decode_any W_a4210 = Some (Auipc 10 1048433, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4214 : bv 32 := 0x01300593.
Lemma F_a4214 : fetch_word AsanUbsan.M.loaded_segments (0xa4214 : word) = Some W_a4214.
Proof. vm_refl. Qed.
Lemma D_a4214 : decode_any W_a4214 = Some (OpImm ALU_ADD 11 0 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4218 : bv 32 := 0x0ba50513.
Lemma F_a4218 : fetch_word AsanUbsan.M.loaded_segments (0xa4218 : word) = Some W_a4218.
Proof. vm_refl. Qed.
Lemma D_a4218 : decode_any W_a4218 = Some (OpImm ALU_ADD 10 10 186, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a421c : bv 32 := 0x00100613.
Lemma F_a421c : fetch_word AsanUbsan.M.loaded_segments (0xa421c : word) = Some W_a421c.
Proof. vm_refl. Qed.
Lemma D_a421c : decode_any W_a421c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4220 : bv 32 := 0x8a4bd0ef.
Lemma F_a4220 : fetch_word AsanUbsan.M.loaded_segments (0xa4220 : word) = Some W_a4220.
Proof. vm_refl. Qed.
Lemma D_a4220 : decode_any W_a4220 = Some (Jal 1 1822884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4224 : bv 32 := 0x00200513.
Lemma F_a4224 : fetch_word AsanUbsan.M.loaded_segments (0xa4224 : word) = Some W_a4224.
Proof. vm_refl. Qed.
Lemma D_a4224 : decode_any W_a4224 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4228 : bv 32 := 0x3c05f0ef.
Lemma F_a4228 : fetch_word AsanUbsan.M.loaded_segments (0xa4228 : word) = Some W_a4228.
Proof. vm_refl. Qed.
Lemma D_a4228 : decode_any W_a4228 = Some (Jal 1 390080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a422c : bv 32 := 0x0007c517.
Lemma F_a422c : fetch_word AsanUbsan.M.loaded_segments (0xa422c : word) = Some W_a422c.
Proof. vm_refl. Qed.
Lemma D_a422c : decode_any W_a422c = Some (Auipc 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4230 : bv 32 := 0x0bc53503.
Lemma F_a4230 : fetch_word AsanUbsan.M.loaded_segments (0xa4230 : word) = Some W_a4230.
Proof. vm_refl. Qed.
Lemma D_a4230 : decode_any W_a4230 = Some (Load SZ8 true 10 10 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4234 : bv 32 := 0x00053503.
Lemma F_a4234 : fetch_word AsanUbsan.M.loaded_segments (0xa4234 : word) = Some W_a4234.
Proof. vm_refl. Qed.
Lemma D_a4234 : decode_any W_a4234 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4238 : bv 32 := 0xfff7c597.
Lemma F_a4238 : fetch_word AsanUbsan.M.loaded_segments (0xa4238 : word) = Some W_a4238.
Proof. vm_refl. Qed.
Lemma D_a4238 : decode_any W_a4238 = Some (Auipc 11 1048444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a423c : bv 32 := 0x30458593.
Lemma F_a423c : fetch_word AsanUbsan.M.loaded_segments (0xa423c : word) = Some W_a423c.
Proof. vm_refl. Qed.
Lemma D_a423c : decode_any W_a423c = Some (OpImm ALU_ADD 11 11 772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4240 : bv 32 := 0xf9dff06f.
Lemma F_a4240 : fetch_word AsanUbsan.M.loaded_segments (0xa4240 : word) = Some W_a4240.
Proof. vm_refl. Qed.
Lemma D_a4240 : decode_any W_a4240 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4244 : bv 32 := 0x0007c517.
Lemma F_a4244 : fetch_word AsanUbsan.M.loaded_segments (0xa4244 : word) = Some W_a4244.
Proof. vm_refl. Qed.
Lemma D_a4244 : decode_any W_a4244 = Some (Auipc 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4248 : bv 32 := 0x0a453503.
Lemma F_a4248 : fetch_word AsanUbsan.M.loaded_segments (0xa4248 : word) = Some W_a4248.
Proof. vm_refl. Qed.
Lemma D_a4248 : decode_any W_a4248 = Some (Load SZ8 true 10 10 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a424c : bv 32 := 0x00053683.
Lemma F_a424c : fetch_word AsanUbsan.M.loaded_segments (0xa424c : word) = Some W_a424c.
Proof. vm_refl. Qed.
Lemma D_a424c : decode_any W_a424c = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4250 : bv 32 := 0xfff71517.
Lemma F_a4250 : fetch_word AsanUbsan.M.loaded_segments (0xa4250 : word) = Some W_a4250.
Proof. vm_refl. Qed.
Lemma D_a4250 : decode_any W_a4250 = Some (Auipc 10 1048433, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4254 : bv 32 := 0x01300593.
Lemma F_a4254 : fetch_word AsanUbsan.M.loaded_segments (0xa4254 : word) = Some W_a4254.
Proof. vm_refl. Qed.
Lemma D_a4254 : decode_any W_a4254 = Some (OpImm ALU_ADD 11 0 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4258 : bv 32 := 0x07a50513.
Lemma F_a4258 : fetch_word AsanUbsan.M.loaded_segments (0xa4258 : word) = Some W_a4258.
Proof. vm_refl. Qed.
Lemma D_a4258 : decode_any W_a4258 = Some (OpImm ALU_ADD 10 10 122, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a425c : bv 32 := 0xfc1ff06f.
Lemma F_a425c : fetch_word AsanUbsan.M.loaded_segments (0xa425c : word) = Some W_a425c.
Proof. vm_refl. Qed.
Lemma D_a425c : decode_any W_a425c = Some (Jal 0 2097088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4260 : bv 32 := 0x00008067.
Lemma F_a4260 : fetch_word AsanUbsan.M.loaded_segments (0xa4260 : word) = Some W_a4260.
Proof. vm_refl. Qed.
Lemma D_a4260 : decode_any W_a4260 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4264 : bv 32 := 0x00000513.
Lemma F_a4264 : fetch_word AsanUbsan.M.loaded_segments (0xa4264 : word) = Some W_a4264.
Proof. vm_refl. Qed.
Lemma D_a4264 : decode_any W_a4264 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4268 : bv 32 := 0x00008067.
Lemma F_a4268 : fetch_word AsanUbsan.M.loaded_segments (0xa4268 : word) = Some W_a4268.
Proof. vm_refl. Qed.
Lemma D_a4268 : decode_any W_a4268 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a426c : bv 32 := 0xfb010113.
Lemma F_a426c : fetch_word AsanUbsan.M.loaded_segments (0xa426c : word) = Some W_a426c.
Proof. vm_refl. Qed.
Lemma D_a426c : decode_any W_a426c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4270 : bv 32 := 0x04113423.
Lemma F_a4270 : fetch_word AsanUbsan.M.loaded_segments (0xa4270 : word) = Some W_a4270.
Proof. vm_refl. Qed.
Lemma D_a4270 : decode_any W_a4270 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4274 : bv 32 := 0x04813023.
Lemma F_a4274 : fetch_word AsanUbsan.M.loaded_segments (0xa4274 : word) = Some W_a4274.
Proof. vm_refl. Qed.
Lemma D_a4274 : decode_any W_a4274 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4278 : bv 32 := 0x02913c23.
Lemma F_a4278 : fetch_word AsanUbsan.M.loaded_segments (0xa4278 : word) = Some W_a4278.
Proof. vm_refl. Qed.
Lemma D_a4278 : decode_any W_a4278 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a427c : bv 32 := 0x03213823.
Lemma F_a427c : fetch_word AsanUbsan.M.loaded_segments (0xa427c : word) = Some W_a427c.
Proof. vm_refl. Qed.
Lemma D_a427c : decode_any W_a427c = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4280 : bv 32 := 0x03313423.
Lemma F_a4280 : fetch_word AsanUbsan.M.loaded_segments (0xa4280 : word) = Some W_a4280.
Proof. vm_refl. Qed.
Lemma D_a4280 : decode_any W_a4280 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4284 : bv 32 := 0x03413023.
Lemma F_a4284 : fetch_word AsanUbsan.M.loaded_segments (0xa4284 : word) = Some W_a4284.
Proof. vm_refl. Qed.
Lemma D_a4284 : decode_any W_a4284 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4288 : bv 32 := 0x01513c23.
Lemma F_a4288 : fetch_word AsanUbsan.M.loaded_segments (0xa4288 : word) = Some W_a4288.
Proof. vm_refl. Qed.
Lemma D_a4288 : decode_any W_a4288 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a428c : bv 32 := 0x01613823.
Lemma F_a428c : fetch_word AsanUbsan.M.loaded_segments (0xa428c : word) = Some W_a428c.
Proof. vm_refl. Qed.
Lemma D_a428c : decode_any W_a428c = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4290 : bv 32 := 0x01713423.
Lemma F_a4290 : fetch_word AsanUbsan.M.loaded_segments (0xa4290 : word) = Some W_a4290.
Proof. vm_refl. Qed.
Lemma D_a4290 : decode_any W_a4290 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4294 : bv 32 := 0x00068413.
Lemma F_a4294 : fetch_word AsanUbsan.M.loaded_segments (0xa4294 : word) = Some W_a4294.
Proof. vm_refl. Qed.
Lemma D_a4294 : decode_any W_a4294 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4298 : bv 32 := 0x00060493.
Lemma F_a4298 : fetch_word AsanUbsan.M.loaded_segments (0xa4298 : word) = Some W_a4298.
Proof. vm_refl. Qed.
Lemma D_a4298 : decode_any W_a4298 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a429c : bv 32 := 0x00058913.
Lemma F_a429c : fetch_word AsanUbsan.M.loaded_segments (0xa429c : word) = Some W_a429c.
Proof. vm_refl. Qed.
Lemma D_a429c : decode_any W_a429c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42a0 : bv 32 := 0x005bc597.
Lemma F_a42a0 : fetch_word AsanUbsan.M.loaded_segments (0xa42a0 : word) = Some W_a42a0.
Proof. vm_refl. Qed.
Lemma D_a42a0 : decode_any W_a42a0 = Some (Auipc 11 1468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42a4 : bv 32 := 0xb7058a13.
Lemma F_a42a4 : fetch_word AsanUbsan.M.loaded_segments (0xa42a4 : word) = Some W_a42a4.
Proof. vm_refl. Qed.
Lemma D_a42a4 : decode_any W_a42a4 = Some (OpImm ALU_ADD 20 11 2928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42a8 : bv 32 := 0x000a4583.
Lemma F_a42a8 : fetch_word AsanUbsan.M.loaded_segments (0xa42a8 : word) = Some W_a42a8.
Proof. vm_refl. Qed.
Lemma D_a42a8 : decode_any W_a42a8 = Some (Load SZ1 false 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42ac : bv 32 := 0x00050993.
Lemma F_a42ac : fetch_word AsanUbsan.M.loaded_segments (0xa42ac : word) = Some W_a42ac.
Proof. vm_refl. Qed.
Lemma D_a42ac : decode_any W_a42ac = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42b0 : bv 32 := 0x02058e63.
Lemma F_a42b0 : fetch_word AsanUbsan.M.loaded_segments (0xa42b0 : word) = Some W_a42b0.
Proof. vm_refl. Qed.
Lemma D_a42b0 : decode_any W_a42b0 = Some (Branch BC_EQ 11 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42b4 : bv 32 := 0x04090c63.
Lemma F_a42b4 : fetch_word AsanUbsan.M.loaded_segments (0xa42b4 : word) = Some W_a42b4.
Proof. vm_refl. Qed.
Lemma D_a42b4 : decode_any W_a42b4 = Some (Branch BC_EQ 18 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42b8 : bv 32 := 0x0009c503.
Lemma F_a42b8 : fetch_word AsanUbsan.M.loaded_segments (0xa42b8 : word) = Some W_a42b8.
Proof. vm_refl. Qed.
Lemma D_a42b8 : decode_any W_a42b8 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42bc : bv 32 := 0x00357513.
Lemma F_a42bc : fetch_word AsanUbsan.M.loaded_segments (0xa42bc : word) = Some W_a42bc.
Proof. vm_refl. Qed.
Lemma D_a42bc : decode_any W_a42bc = Some (OpImm ALU_AND 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42c0 : bv 32 := 0x00150a93.
Lemma F_a42c0 : fetch_word AsanUbsan.M.loaded_segments (0xa42c0 : word) = Some W_a42c0.
Proof. vm_refl. Qed.
Lemma D_a42c0 : decode_any W_a42c0 = Some (OpImm ALU_ADD 21 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42c4 : bv 32 := 0x04040863.
Lemma F_a42c4 : fetch_word AsanUbsan.M.loaded_segments (0xa42c4 : word) = Some W_a42c4.
Proof. vm_refl. Qed.
Lemma D_a42c4 : decode_any W_a42c4 = Some (Branch BC_EQ 8 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42c8 : bv 32 := 0x00040513.
Lemma F_a42c8 : fetch_word AsanUbsan.M.loaded_segments (0xa42c8 : word) = Some W_a42c8.
Proof. vm_refl. Qed.
Lemma D_a42c8 : decode_any W_a42c8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42cc : bv 32 := 0xa78d00ef.
Lemma F_a42cc : fetch_word AsanUbsan.M.loaded_segments (0xa42cc : word) = Some W_a42cc.
Proof. vm_refl. Qed.
Lemma D_a42cc : decode_any W_a42cc = Some (Jal 1 1901176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42d0 : bv 32 := 0x02050a63.
Lemma F_a42d0 : fetch_word AsanUbsan.M.loaded_segments (0xa42d0 : word) = Some W_a42d0.
Proof. vm_refl. Qed.
Lemma D_a42d0 : decode_any W_a42d0 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42d4 : bv 32 := 0x00050913.
Lemma F_a42d4 : fetch_word AsanUbsan.M.loaded_segments (0xa42d4 : word) = Some W_a42d4.
Proof. vm_refl. Qed.
Lemma D_a42d4 : decode_any W_a42d4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42d8 : bv 32 := 0x00048593.
Lemma F_a42d8 : fetch_word AsanUbsan.M.loaded_segments (0xa42d8 : word) = Some W_a42d8.
Proof. vm_refl. Qed.
Lemma D_a42d8 : decode_any W_a42d8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42dc : bv 32 := 0x00040613.
Lemma F_a42dc : fetch_word AsanUbsan.M.loaded_segments (0xa42dc : word) = Some W_a42dc.
Proof. vm_refl. Qed.
Lemma D_a42dc : decode_any W_a42dc = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42e0 : bv 32 := 0xedcce0ef.
Lemma F_a42e0 : fetch_word AsanUbsan.M.loaded_segments (0xa42e0 : word) = Some W_a42e0.
Proof. vm_refl. Qed.
Lemma D_a42e0 : decode_any W_a42e0 = Some (Jal 1 1894108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42e4 : bv 32 := 0x00090493.
Lemma F_a42e4 : fetch_word AsanUbsan.M.loaded_segments (0xa42e4 : word) = Some W_a42e4.
Proof. vm_refl. Qed.
Lemma D_a42e4 : decode_any W_a42e4 = Some (OpImm ALU_ADD 9 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42e8 : bv 32 := 0x0340006f.
Lemma F_a42e8 : fetch_word AsanUbsan.M.loaded_segments (0xa42e8 : word) = Some W_a42e8.
Proof. vm_refl. Qed.
Lemma D_a42e8 : decode_any W_a42e8 = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42ec : bv 32 := 0x00100513.
Lemma F_a42ec : fetch_word AsanUbsan.M.loaded_segments (0xa42ec : word) = Some W_a42ec.
Proof. vm_refl. Qed.
Lemma D_a42ec : decode_any W_a42ec = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42f0 : bv 32 := 0x00aa0023.
Lemma F_a42f0 : fetch_word AsanUbsan.M.loaded_segments (0xa42f0 : word) = Some W_a42f0.
Proof. vm_refl. Qed.
Lemma D_a42f0 : decode_any W_a42f0 = Some (Store SZ1 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42f4 : bv 32 := 0x00000517.
Lemma F_a42f4 : fetch_word AsanUbsan.M.loaded_segments (0xa42f4 : word) = Some W_a42f4.
Proof. vm_refl. Qed.
Lemma D_a42f4 : decode_any W_a42f4 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42f8 : bv 32 := 0x0d050513.
Lemma F_a42f8 : fetch_word AsanUbsan.M.loaded_segments (0xa42f8 : word) = Some W_a42f8.
Proof. vm_refl. Qed.
Lemma D_a42f8 : decode_any W_a42f8 = Some (OpImm ALU_ADD 10 10 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a42fc : bv 32 := 0x1d45f0ef.
Lemma F_a42fc : fetch_word AsanUbsan.M.loaded_segments (0xa42fc : word) = Some W_a42fc.
Proof. vm_refl. Qed.
Lemma D_a42fc : decode_any W_a42fc = Some (Jal 1 389588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4300 : bv 32 := 0x08050e63.
Lemma F_a4300 : fetch_word AsanUbsan.M.loaded_segments (0xa4300 : word) = Some W_a4300.
Proof. vm_refl. Qed.
Lemma D_a4300 : decode_any W_a4300 = Some (Branch BC_EQ 10 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4304 : bv 32 := 0x00200513.
Lemma F_a4304 : fetch_word AsanUbsan.M.loaded_segments (0xa4304 : word) = Some W_a4304.
Proof. vm_refl. Qed.
Lemma D_a4304 : decode_any W_a4304 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4308 : bv 32 := 0x0680006f.
Lemma F_a4308 : fetch_word AsanUbsan.M.loaded_segments (0xa4308 : word) = Some W_a4308.
Proof. vm_refl. Qed.
Lemma D_a4308 : decode_any W_a4308 = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a430c : bv 32 := 0x00100a93.
Lemma F_a430c : fetch_word AsanUbsan.M.loaded_segments (0xa430c : word) = Some W_a430c.
Proof. vm_refl. Qed.
Lemma D_a430c : decode_any W_a430c = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4310 : bv 32 := 0xfa041ce3.
Lemma F_a4310 : fetch_word AsanUbsan.M.loaded_segments (0xa4310 : word) = Some W_a4310.
Proof. vm_refl. Qed.
Lemma D_a4310 : decode_any W_a4310 = Some (Branch BC_NE 8 0 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4314 : bv 32 := 0x00000913.
Lemma F_a4314 : fetch_word AsanUbsan.M.loaded_segments (0xa4314 : word) = Some W_a4314.
Proof. vm_refl. Qed.
Lemma D_a4314 : decode_any W_a4314 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4318 : bv 32 := 0x010a0493.
Lemma F_a4318 : fetch_word AsanUbsan.M.loaded_segments (0xa4318 : word) = Some W_a4318.
Proof. vm_refl. Qed.
Lemma D_a4318 : decode_any W_a4318 = Some (OpImm ALU_ADD 9 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a431c : bv 32 := 0x00000b13.
Lemma F_a431c : fetch_word AsanUbsan.M.loaded_segments (0xa431c : word) = Some W_a431c.
Proof. vm_refl. Qed.
Lemma D_a431c : decode_any W_a431c = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4320 : bv 32 := 0xffe00b93.
Lemma F_a4320 : fetch_word AsanUbsan.M.loaded_segments (0xa4320 : word) = Some W_a4320.
Proof. vm_refl. Qed.
Lemma D_a4320 : decode_any W_a4320 = Some (OpImm ALU_ADD 23 0 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4324 : bv 32 := 0x00100513.
Lemma F_a4324 : fetch_word AsanUbsan.M.loaded_segments (0xa4324 : word) = Some W_a4324.
Proof. vm_refl. Qed.
Lemma D_a4324 : decode_any W_a4324 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4328 : bv 32 := 0x00aa0223.
Lemma F_a4328 : fetch_word AsanUbsan.M.loaded_segments (0xa4328 : word) = Some W_a4328.
Proof. vm_refl. Qed.
Lemma D_a4328 : decode_any W_a4328 = Some (Store SZ1 20 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a432c : bv 32 := 0x00048513.
Lemma F_a432c : fetch_word AsanUbsan.M.loaded_segments (0xa432c : word) = Some W_a432c.
Proof. vm_refl. Qed.
Lemma D_a432c : decode_any W_a432c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4330 : bv 32 := 0x00040593.
Lemma F_a4330 : fetch_word AsanUbsan.M.loaded_segments (0xa4330 : word) = Some W_a4330.
Proof. vm_refl. Qed.
Lemma D_a4330 : decode_any W_a4330 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4334 : bv 32 := 0x7bc000ef.
Lemma F_a4334 : fetch_word AsanUbsan.M.loaded_segments (0xa4334 : word) = Some W_a4334.
Proof. vm_refl. Qed.
Lemma D_a4334 : decode_any W_a4334 = Some (Jal 1 1980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4338 : bv 32 := 0x00050993.
Lemma F_a4338 : fetch_word AsanUbsan.M.loaded_segments (0xa4338 : word) = Some W_a4338.
Proof. vm_refl. Qed.
Lemma D_a4338 : decode_any W_a4338 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a433c : bv 32 := 0x000a0223.
Lemma F_a433c : fetch_word AsanUbsan.M.loaded_segments (0xa433c : word) = Some W_a433c.
Proof. vm_refl. Qed.
Lemma D_a433c : decode_any W_a433c = Some (Store SZ1 20 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4340 : bv 32 := 0x00050593.
Lemma F_a4340 : fetch_word AsanUbsan.M.loaded_segments (0xa4340 : word) = Some W_a4340.
Proof. vm_refl. Qed.
Lemma D_a4340 : decode_any W_a4340 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4344 : bv 32 := 0x0b0000ef.
Lemma F_a4344 : fetch_word AsanUbsan.M.loaded_segments (0xa4344 : word) = Some W_a4344.
Proof. vm_refl. Qed.
Lemma D_a4344 : decode_any W_a4344 = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4348 : bv 32 := 0xfff9899b.
Lemma F_a4348 : fetch_word AsanUbsan.M.loaded_segments (0xa4348 : word) = Some W_a4348.
Proof. vm_refl. Qed.
Lemma D_a4348 : decode_any W_a4348 = Some (OpImm32 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a434c : bv 32 := 0x0179f463.
Lemma F_a434c : fetch_word AsanUbsan.M.loaded_segments (0xa434c : word) = Some W_a434c.
Proof. vm_refl. Qed.
Lemma D_a434c : decode_any W_a434c = Some (Branch BC_GEU 19 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4350 : bv 32 := 0x00100b13.
Lemma F_a4350 : fetch_word AsanUbsan.M.loaded_segments (0xa4350 : word) = Some W_a4350.
Proof. vm_refl. Qed.
Lemma D_a4350 : decode_any W_a4350 = Some (OpImm ALU_ADD 22 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4354 : bv 32 := 0xfffa8a9b.
Lemma F_a4354 : fetch_word AsanUbsan.M.loaded_segments (0xa4354 : word) = Some W_a4354.
Proof. vm_refl. Qed.
Lemma D_a4354 : decode_any W_a4354 = Some (OpImm32 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4358 : bv 32 := 0xfc0a96e3.
Lemma F_a4358 : fetch_word AsanUbsan.M.loaded_segments (0xa4358 : word) = Some W_a4358.
Proof. vm_refl. Qed.
Lemma D_a4358 : decode_any W_a4358 = Some (Branch BC_NE 21 0 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a435c : bv 32 := 0x00090513.
Lemma F_a435c : fetch_word AsanUbsan.M.loaded_segments (0xa435c : word) = Some W_a435c.
Proof. vm_refl. Qed.
Lemma D_a435c : decode_any W_a435c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4360 : bv 32 := 0x9e0d00ef.
Lemma F_a4360 : fetch_word AsanUbsan.M.loaded_segments (0xa4360 : word) = Some W_a4360.
Proof. vm_refl. Qed.
Lemma D_a4360 : decode_any W_a4360 = Some (Jal 1 1901024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4364 : bv 32 := 0x001b3513.
Lemma F_a4364 : fetch_word AsanUbsan.M.loaded_segments (0xa4364 : word) = Some W_a4364.
Proof. vm_refl. Qed.
Lemma D_a4364 : decode_any W_a4364 = Some (OpImm ALU_SLTU 10 22 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4368 : bv 32 := 0xfff50513.
Lemma F_a4368 : fetch_word AsanUbsan.M.loaded_segments (0xa4368 : word) = Some W_a4368.
Proof. vm_refl. Qed.
Lemma D_a4368 : decode_any W_a4368 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a436c : bv 32 := 0x04e57513.
Lemma F_a436c : fetch_word AsanUbsan.M.loaded_segments (0xa436c : word) = Some W_a436c.
Proof. vm_refl. Qed.
Lemma D_a436c : decode_any W_a436c = Some (OpImm ALU_AND 10 10 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4370 : bv 32 := 0x04813083.
Lemma F_a4370 : fetch_word AsanUbsan.M.loaded_segments (0xa4370 : word) = Some W_a4370.
Proof. vm_refl. Qed.
Lemma D_a4370 : decode_any W_a4370 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4374 : bv 32 := 0x04013403.
Lemma F_a4374 : fetch_word AsanUbsan.M.loaded_segments (0xa4374 : word) = Some W_a4374.
Proof. vm_refl. Qed.
Lemma D_a4374 : decode_any W_a4374 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4378 : bv 32 := 0x03813483.
Lemma F_a4378 : fetch_word AsanUbsan.M.loaded_segments (0xa4378 : word) = Some W_a4378.
Proof. vm_refl. Qed.
Lemma D_a4378 : decode_any W_a4378 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a437c : bv 32 := 0x03013903.
Lemma F_a437c : fetch_word AsanUbsan.M.loaded_segments (0xa437c : word) = Some W_a437c.
Proof. vm_refl. Qed.
Lemma D_a437c : decode_any W_a437c = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4380 : bv 32 := 0x02813983.
Lemma F_a4380 : fetch_word AsanUbsan.M.loaded_segments (0xa4380 : word) = Some W_a4380.
Proof. vm_refl. Qed.
Lemma D_a4380 : decode_any W_a4380 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4384 : bv 32 := 0x02013a03.
Lemma F_a4384 : fetch_word AsanUbsan.M.loaded_segments (0xa4384 : word) = Some W_a4384.
Proof. vm_refl. Qed.
Lemma D_a4384 : decode_any W_a4384 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4388 : bv 32 := 0x01813a83.
Lemma F_a4388 : fetch_word AsanUbsan.M.loaded_segments (0xa4388 : word) = Some W_a4388.
Proof. vm_refl. Qed.
Lemma D_a4388 : decode_any W_a4388 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a438c : bv 32 := 0x01013b03.
Lemma F_a438c : fetch_word AsanUbsan.M.loaded_segments (0xa438c : word) = Some W_a438c.
Proof. vm_refl. Qed.
Lemma D_a438c : decode_any W_a438c = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4390 : bv 32 := 0x00813b83.
Lemma F_a4390 : fetch_word AsanUbsan.M.loaded_segments (0xa4390 : word) = Some W_a4390.
Proof. vm_refl. Qed.
Lemma D_a4390 : decode_any W_a4390 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4394 : bv 32 := 0x05010113.
Lemma F_a4394 : fetch_word AsanUbsan.M.loaded_segments (0xa4394 : word) = Some W_a4394.
Proof. vm_refl. Qed.
Lemma D_a4394 : decode_any W_a4394 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4398 : bv 32 := 0x00008067.
Lemma F_a4398 : fetch_word AsanUbsan.M.loaded_segments (0xa4398 : word) = Some W_a4398.
Proof. vm_refl. Qed.
Lemma D_a4398 : decode_any W_a4398 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a439c : bv 32 := 0x0007c517.
Lemma F_a439c : fetch_word AsanUbsan.M.loaded_segments (0xa439c : word) = Some W_a439c.
Proof. vm_refl. Qed.
Lemma D_a439c : decode_any W_a439c = Some (Auipc 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43a0 : bv 32 := 0xf5453503.
Lemma F_a43a0 : fetch_word AsanUbsan.M.loaded_segments (0xa43a0 : word) = Some W_a43a0.
Proof. vm_refl. Qed.
Lemma D_a43a0 : decode_any W_a43a0 = Some (Load SZ8 true 10 10 3924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43a4 : bv 32 := 0xf00508e3.
Lemma F_a43a4 : fetch_word AsanUbsan.M.loaded_segments (0xa43a4 : word) = Some W_a43a4.
Proof. vm_refl. Qed.
Lemma D_a43a4 : decode_any W_a43a4 = Some (Branch BC_EQ 10 0 7952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43a8 : bv 32 := 0x00080517.
Lemma F_a43a8 : fetch_word AsanUbsan.M.loaded_segments (0xa43a8 : word) = Some W_a43a8.
Proof. vm_refl. Qed.
Lemma D_a43a8 : decode_any W_a43a8 = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43ac : bv 32 := 0x97050513.
Lemma F_a43ac : fetch_word AsanUbsan.M.loaded_segments (0xa43ac : word) = Some W_a43ac.
Proof. vm_refl. Qed.
Lemma D_a43ac : decode_any W_a43ac = Some (OpImm ALU_ADD 10 10 2416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43b0 : bv 32 := 0x00850593.
Lemma F_a43b0 : fetch_word AsanUbsan.M.loaded_segments (0xa43b0 : word) = Some W_a43b0.
Proof. vm_refl. Qed.
Lemma D_a43b0 : decode_any W_a43b0 = Some (OpImm ALU_ADD 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43b4 : bv 32 := 0x00b13023.
Lemma F_a43b4 : fetch_word AsanUbsan.M.loaded_segments (0xa43b4 : word) = Some W_a43b4.
Proof. vm_refl. Qed.
Lemma D_a43b4 : decode_any W_a43b4 = Some (Store SZ8 2 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43b8 : bv 32 := 0x00010593.
Lemma F_a43b8 : fetch_word AsanUbsan.M.loaded_segments (0xa43b8 : word) = Some W_a43b8.
Proof. vm_refl. Qed.
Lemma D_a43b8 : decode_any W_a43b8 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43bc : bv 32 := 0x000000ef.
Lemma F_a43bc : fetch_word AsanUbsan.M.loaded_segments (0xa43bc : word) = Some W_a43bc.
Proof. vm_refl. Qed.
Lemma D_a43bc : decode_any W_a43bc = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43c0 : bv 32 := 0xef5ff06f.
Lemma F_a43c0 : fetch_word AsanUbsan.M.loaded_segments (0xa43c0 : word) = Some W_a43c0.
Proof. vm_refl. Qed.
Lemma D_a43c0 : decode_any W_a43c0 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43c4 : bv 32 := 0x005bc517.
Lemma F_a43c4 : fetch_word AsanUbsan.M.loaded_segments (0xa43c4 : word) = Some W_a43c4.
Proof. vm_refl. Qed.
Lemma D_a43c4 : decode_any W_a43c4 = Some (Auipc 10 1468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43c8 : bv 32 := 0xa5054503.
Lemma F_a43c8 : fetch_word AsanUbsan.M.loaded_segments (0xa43c8 : word) = Some W_a43c8.
Proof. vm_refl. Qed.
Lemma D_a43c8 : decode_any W_a43c8 = Some (Load SZ1 false 10 10 2640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43cc : bv 32 := 0x00051463.
Lemma F_a43cc : fetch_word AsanUbsan.M.loaded_segments (0xa43cc : word) = Some W_a43cc.
Proof. vm_refl. Qed.
Lemma D_a43cc : decode_any W_a43cc = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43d0 : bv 32 := 0x00008067.
Lemma F_a43d0 : fetch_word AsanUbsan.M.loaded_segments (0xa43d0 : word) = Some W_a43d0.
Proof. vm_refl. Qed.
Lemma D_a43d0 : decode_any W_a43d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43d4 : bv 32 := 0xff010113.
Lemma F_a43d4 : fetch_word AsanUbsan.M.loaded_segments (0xa43d4 : word) = Some W_a43d4.
Proof. vm_refl. Qed.
Lemma D_a43d4 : decode_any W_a43d4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43d8 : bv 32 := 0x00113423.
Lemma F_a43d8 : fetch_word AsanUbsan.M.loaded_segments (0xa43d8 : word) = Some W_a43d8.
Proof. vm_refl. Qed.
Lemma D_a43d8 : decode_any W_a43d8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43dc : bv 32 := 0x0007c517.
Lemma F_a43dc : fetch_word AsanUbsan.M.loaded_segments (0xa43dc : word) = Some W_a43dc.
Proof. vm_refl. Qed.
Lemma D_a43dc : decode_any W_a43dc = Some (Auipc 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43e0 : bv 32 := 0xf1c53503.
Lemma F_a43e0 : fetch_word AsanUbsan.M.loaded_segments (0xa43e0 : word) = Some W_a43e0.
Proof. vm_refl. Qed.
Lemma D_a43e0 : decode_any W_a43e0 = Some (Load SZ8 true 10 10 3868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43e4 : bv 32 := 0x00053503.
Lemma F_a43e4 : fetch_word AsanUbsan.M.loaded_segments (0xa43e4 : word) = Some W_a43e4.
Proof. vm_refl. Qed.
Lemma D_a43e4 : decode_any W_a43e4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43e8 : bv 32 := 0xf25bc0ef.
Lemma F_a43e8 : fetch_word AsanUbsan.M.loaded_segments (0xa43e8 : word) = Some W_a43e8.
Proof. vm_refl. Qed.
Lemma D_a43e8 : decode_any W_a43e8 = Some (Jal 1 1822500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43ec : bv 32 := 0x04d00513.
Lemma F_a43ec : fetch_word AsanUbsan.M.loaded_segments (0xa43ec : word) = Some W_a43ec.
Proof. vm_refl. Qed.
Lemma D_a43ec : decode_any W_a43ec = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43f0 : bv 32 := 0xf11bc0ef.
Lemma F_a43f0 : fetch_word AsanUbsan.M.loaded_segments (0xa43f0 : word) = Some W_a43f0.
Proof. vm_refl. Qed.
Lemma D_a43f0 : decode_any W_a43f0 = Some (Jal 1 1822480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43f4 : bv 32 := 0xfb010113.
Lemma F_a43f4 : fetch_word AsanUbsan.M.loaded_segments (0xa43f4 : word) = Some W_a43f4.
Proof. vm_refl. Qed.
Lemma D_a43f4 : decode_any W_a43f4 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43f8 : bv 32 := 0x00113423.
Lemma F_a43f8 : fetch_word AsanUbsan.M.loaded_segments (0xa43f8 : word) = Some W_a43f8.
Proof. vm_refl. Qed.
Lemma D_a43f8 : decode_any W_a43f8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a43fc : bv 32 := 0x02f13c23.
Lemma F_a43fc : fetch_word AsanUbsan.M.loaded_segments (0xa43fc : word) = Some W_a43fc.
Proof. vm_refl. Qed.
Lemma D_a43fc : decode_any W_a43fc = Some (Store SZ8 2 15 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4400 : bv 32 := 0x05013023.
Lemma F_a4400 : fetch_word AsanUbsan.M.loaded_segments (0xa4400 : word) = Some W_a4400.
Proof. vm_refl. Qed.
Lemma D_a4400 : decode_any W_a4400 = Some (Store SZ8 2 16 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4404 : bv 32 := 0x05113423.
Lemma F_a4404 : fetch_word AsanUbsan.M.loaded_segments (0xa4404 : word) = Some W_a4404.
Proof. vm_refl. Qed.
Lemma D_a4404 : decode_any W_a4404 = Some (Store SZ8 2 17 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4408 : bv 32 := 0x00b13c23.
Lemma F_a4408 : fetch_word AsanUbsan.M.loaded_segments (0xa4408 : word) = Some W_a4408.
Proof. vm_refl. Qed.
Lemma D_a4408 : decode_any W_a4408 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a440c : bv 32 := 0x02c13023.
Lemma F_a440c : fetch_word AsanUbsan.M.loaded_segments (0xa440c : word) = Some W_a440c.
Proof. vm_refl. Qed.
Lemma D_a440c : decode_any W_a440c = Some (Store SZ8 2 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4410 : bv 32 := 0x02d13423.
Lemma F_a4410 : fetch_word AsanUbsan.M.loaded_segments (0xa4410 : word) = Some W_a4410.
Proof. vm_refl. Qed.
Lemma D_a4410 : decode_any W_a4410 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4414 : bv 32 := 0x02e13823.
Lemma F_a4414 : fetch_word AsanUbsan.M.loaded_segments (0xa4414 : word) = Some W_a4414.
Proof. vm_refl. Qed.
Lemma D_a4414 : decode_any W_a4414 = Some (Store SZ8 2 14 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4418 : bv 32 := 0x01810513.
Lemma F_a4418 : fetch_word AsanUbsan.M.loaded_segments (0xa4418 : word) = Some W_a4418.
Proof. vm_refl. Qed.
Lemma D_a4418 : decode_any W_a4418 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a441c : bv 32 := 0x00a13023.
Lemma F_a441c : fetch_word AsanUbsan.M.loaded_segments (0xa441c : word) = Some W_a441c.
Proof. vm_refl. Qed.
Lemma D_a441c : decode_any W_a441c = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4420 : bv 32 := 0xfff71517.
Lemma F_a4420 : fetch_word AsanUbsan.M.loaded_segments (0xa4420 : word) = Some W_a4420.
Proof. vm_refl. Qed.
Lemma D_a4420 : decode_any W_a4420 = Some (Auipc 10 1048433, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4424 : bv 32 := 0xebe50513.
Lemma F_a4424 : fetch_word AsanUbsan.M.loaded_segments (0xa4424 : word) = Some W_a4424.
Proof. vm_refl. Qed.
Lemma D_a4424 : decode_any W_a4424 = Some (OpImm ALU_ADD 10 10 3774, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4428 : bv 32 := 0x01810593.
Lemma F_a4428 : fetch_word AsanUbsan.M.loaded_segments (0xa4428 : word) = Some W_a4428.
Proof. vm_refl. Qed.
Lemma D_a4428 : decode_any W_a4428 = Some (OpImm ALU_ADD 11 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a442c : bv 32 := 0xea5bc0ef.
Lemma F_a442c : fetch_word AsanUbsan.M.loaded_segments (0xa442c : word) = Some W_a442c.
Proof. vm_refl. Qed.
Lemma D_a442c : decode_any W_a442c = Some (Jal 1 1822372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4430 : bv 32 := 0x00813083.
Lemma F_a4430 : fetch_word AsanUbsan.M.loaded_segments (0xa4430 : word) = Some W_a4430.
Proof. vm_refl. Qed.
Lemma D_a4430 : decode_any W_a4430 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4434 : bv 32 := 0x05010113.
Lemma F_a4434 : fetch_word AsanUbsan.M.loaded_segments (0xa4434 : word) = Some W_a4434.
Proof. vm_refl. Qed.
Lemma D_a4434 : decode_any W_a4434 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4438 : bv 32 := 0x00008067.
Lemma F_a4438 : fetch_word AsanUbsan.M.loaded_segments (0xa4438 : word) = Some W_a4438.
Proof. vm_refl. Qed.
Lemma D_a4438 : decode_any W_a4438 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
