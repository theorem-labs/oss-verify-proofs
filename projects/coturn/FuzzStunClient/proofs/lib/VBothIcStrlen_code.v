(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_44220 : bv 32 := 0x0940006f.
Lemma F_44220 : fetch_word AsanUbsan.M.loaded_segments (0x44220 : word) = Some W_44220.
Proof. vm_refl. Qed.
Lemma D_44220 : decode_any W_44220 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_442b4 : bv 32 := 0x81010113.
Lemma F_442b4 : fetch_word AsanUbsan.M.loaded_segments (0x442b4 : word) = Some W_442b4.
Proof. vm_refl. Qed.
Lemma D_442b4 : decode_any W_442b4 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442b8 : bv 32 := 0x7e113423.
Lemma F_442b8 : fetch_word AsanUbsan.M.loaded_segments (0x442b8 : word) = Some W_442b8.
Proof. vm_refl. Qed.
Lemma D_442b8 : decode_any W_442b8 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442bc : bv 32 := 0x7e813023.
Lemma F_442bc : fetch_word AsanUbsan.M.loaded_segments (0x442bc : word) = Some W_442bc.
Proof. vm_refl. Qed.
Lemma D_442bc : decode_any W_442bc = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442c0 : bv 32 := 0x7c913c23.
Lemma F_442c0 : fetch_word AsanUbsan.M.loaded_segments (0x442c0 : word) = Some W_442c0.
Proof. vm_refl. Qed.
Lemma D_442c0 : decode_any W_442c0 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442c4 : bv 32 := 0x7d213823.
Lemma F_442c4 : fetch_word AsanUbsan.M.loaded_segments (0x442c4 : word) = Some W_442c4.
Proof. vm_refl. Qed.
Lemma D_442c4 : decode_any W_442c4 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442c8 : bv 32 := 0x7d313423.
Lemma F_442c8 : fetch_word AsanUbsan.M.loaded_segments (0x442c8 : word) = Some W_442c8.
Proof. vm_refl. Qed.
Lemma D_442c8 : decode_any W_442c8 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442cc : bv 32 := 0x7d413023.
Lemma F_442cc : fetch_word AsanUbsan.M.loaded_segments (0x442cc : word) = Some W_442cc.
Proof. vm_refl. Qed.
Lemma D_442cc : decode_any W_442cc = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442d0 : bv 32 := 0x7b513c23.
Lemma F_442d0 : fetch_word AsanUbsan.M.loaded_segments (0x442d0 : word) = Some W_442d0.
Proof. vm_refl. Qed.
Lemma D_442d0 : decode_any W_442d0 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442d4 : bv 32 := 0x7b613823.
Lemma F_442d4 : fetch_word AsanUbsan.M.loaded_segments (0x442d4 : word) = Some W_442d4.
Proof. vm_refl. Qed.
Lemma D_442d4 : decode_any W_442d4 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442d8 : bv 32 := 0x7f010413.
Lemma F_442d8 : fetch_word AsanUbsan.M.loaded_segments (0x442d8 : word) = Some W_442d8.
Proof. vm_refl. Qed.
Lemma D_442d8 : decode_any W_442d8 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442dc : bv 32 := 0xf9010113.
Lemma F_442dc : fetch_word AsanUbsan.M.loaded_segments (0x442dc : word) = Some W_442dc.
Proof. vm_refl. Qed.
Lemma D_442dc : decode_any W_442dc = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442e0 : bv 32 := 0x00050913.
Lemma F_442e0 : fetch_word AsanUbsan.M.loaded_segments (0x442e0 : word) = Some W_442e0.
Proof. vm_refl. Qed.
Lemma D_442e0 : decode_any W_442e0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442e4 : bv 32 := 0x43d160ef.
Lemma F_442e4 : fetch_word AsanUbsan.M.loaded_segments (0x442e4 : word) = Some W_442e4.
Proof. vm_refl. Qed.
Lemma D_442e4 : decode_any W_442e4 = Some (Jal 1 93244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442e8 : bv 32 := 0x0a050863.
Lemma F_442e8 : fetch_word AsanUbsan.M.loaded_segments (0x442e8 : word) = Some W_442e8.
Proof. vm_refl. Qed.
Lemma D_442e8 : decode_any W_442e8 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442ec : bv 32 := 0x345170ef.
Lemma F_442ec : fetch_word AsanUbsan.M.loaded_segments (0x442ec : word) = Some W_442ec.
Proof. vm_refl. Qed.
Lemma D_442ec : decode_any W_442ec = Some (Jal 1 97092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442f0 : bv 32 := 0x00067597.
Lemma F_442f0 : fetch_word AsanUbsan.M.loaded_segments (0x442f0 : word) = Some W_442f0.
Proof. vm_refl. Qed.
Lemma D_442f0 : decode_any W_442f0 = Some (Auipc 11 103, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442f4 : bv 32 := 0xed85b583.
Lemma F_442f4 : fetch_word AsanUbsan.M.loaded_segments (0x442f4 : word) = Some W_442f4.
Proof. vm_refl. Qed.
Lemma D_442f4 : decode_any W_442f4 = Some (Load SZ8 true 11 11 3800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442f8 : bv 32 := 0x00050493.
Lemma F_442f8 : fetch_word AsanUbsan.M.loaded_segments (0x442f8 : word) = Some W_442f8.
Proof. vm_refl. Qed.
Lemma D_442f8 : decode_any W_442f8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_442fc : bv 32 := 0x00090513.
Lemma F_442fc : fetch_word AsanUbsan.M.loaded_segments (0x442fc : word) = Some W_442fc.
Proof. vm_refl. Qed.
Lemma D_442fc : decode_any W_442fc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44300 : bv 32 := 0x000580e7.
Lemma F_44300 : fetch_word AsanUbsan.M.loaded_segments (0x44300 : word) = Some W_44300.
Proof. vm_refl. Qed.
Lemma D_44300 : decode_any W_44300 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44304 : bv 32 := 0x06048463.
Lemma F_44304 : fetch_word AsanUbsan.M.loaded_segments (0x44304 : word) = Some W_44304.
Proof. vm_refl. Qed.
Lemma D_44304 : decode_any W_44304 = Some (Branch BC_EQ 9 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44308 : bv 32 := 0x00065597.
Lemma F_44308 : fetch_word AsanUbsan.M.loaded_segments (0x44308 : word) = Some W_44308.
Proof. vm_refl. Qed.
Lemma D_44308 : decode_any W_44308 = Some (Auipc 11 101, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4430c : bv 32 := 0x1a05b983.
Lemma F_4430c : fetch_word AsanUbsan.M.loaded_segments (0x4430c : word) = Some W_4430c.
Proof. vm_refl. Qed.
Lemma D_4430c : decode_any W_4430c = Some (Load SZ8 true 19 11 416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44310 : bv 32 := 0x0fb9c583.
Lemma F_44310 : fetch_word AsanUbsan.M.loaded_segments (0x44310 : word) = Some W_44310.
Proof. vm_refl. Qed.
Lemma D_44310 : decode_any W_44310 = Some (Load SZ1 false 11 19 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44314 : bv 32 := 0x04058c63.
Lemma F_44314 : fetch_word AsanUbsan.M.loaded_segments (0x44314 : word) = Some W_44314.
Proof. vm_refl. Qed.
Lemma D_44314 : decode_any W_44314 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44318 : bv 32 := 0x00150493.
Lemma F_44318 : fetch_word AsanUbsan.M.loaded_segments (0x44318 : word) = Some W_44318.
Proof. vm_refl. Qed.
Lemma D_44318 : decode_any W_44318 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4431c : bv 32 := 0xfff94593.
Lemma F_4431c : fetch_word AsanUbsan.M.loaded_segments (0x4431c : word) = Some W_4431c.
Proof. vm_refl. Qed.
Lemma D_4431c : decode_any W_4431c = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44320 : bv 32 := 0x80040a13.
Lemma F_44320 : fetch_word AsanUbsan.M.loaded_segments (0x44320 : word) = Some W_44320.
Proof. vm_refl. Qed.
Lemma D_44320 : decode_any W_44320 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44324 : bv 32 := 0xfa8a0a13.
Lemma F_44324 : fetch_word AsanUbsan.M.loaded_segments (0x44324 : word) = Some W_44324.
Proof. vm_refl. Qed.
Lemma D_44324 : decode_any W_44324 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44328 : bv 32 := 0x0a95e063.
Lemma F_44328 : fetch_word AsanUbsan.M.loaded_segments (0x44328 : word) = Some W_44328.
Proof. vm_refl. Qed.
Lemma D_44328 : decode_any W_44328 = Some (Branch BC_LTU 11 9 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4432c : bv 32 := 0x04000593.
Lemma F_4432c : fetch_word AsanUbsan.M.loaded_segments (0x4432c : word) = Some W_4432c.
Proof. vm_refl. Qed.
Lemma D_4432c : decode_any W_4432c = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44330 : bv 32 := 0x10b57263.
Lemma F_44330 : fetch_word AsanUbsan.M.loaded_segments (0x44330 : word) = Some W_44330.
Proof. vm_refl. Qed.
Lemma D_44330 : decode_any W_44330 = Some (Branch BC_GEU 10 11 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44334 : bv 32 := 0x00065597.
Lemma F_44334 : fetch_word AsanUbsan.M.loaded_segments (0x44334 : word) = Some W_44334.
Proof. vm_refl. Qed.
Lemma D_44334 : decode_any W_44334 = Some (Auipc 11 101, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44338 : bv 32 := 0x1845b583.
Lemma F_44338 : fetch_word AsanUbsan.M.loaded_segments (0x44338 : word) = Some W_44338.
Proof. vm_refl. Qed.
Lemma D_44338 : decode_any W_44338 = Some (Load SZ8 true 11 11 388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4433c : bv 32 := 0x0005b603.
Lemma F_4433c : fetch_word AsanUbsan.M.loaded_segments (0x4433c : word) = Some W_4433c.
Proof. vm_refl. Qed.
Lemma D_4433c : decode_any W_4433c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44340 : bv 32 := 0x012506b3.
Lemma F_44340 : fetch_word AsanUbsan.M.loaded_segments (0x44340 : word) = Some W_44340.
Proof. vm_refl. Qed.
Lemma D_44340 : decode_any W_44340 = Some (Op ALU_ADD 13 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44344 : bv 32 := 0x00395593.
Lemma F_44344 : fetch_word AsanUbsan.M.loaded_segments (0x44344 : word) = Some W_44344.
Proof. vm_refl. Qed.
Lemma D_44344 : decode_any W_44344 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44348 : bv 32 := 0x0036d713.
Lemma F_44348 : fetch_word AsanUbsan.M.loaded_segments (0x44348 : word) = Some W_44348.
Proof. vm_refl. Qed.
Lemma D_44348 : decode_any W_44348 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4434c : bv 32 := 0x00b605b3.
Lemma F_4434c : fetch_word AsanUbsan.M.loaded_segments (0x4434c : word) = Some W_4434c.
Proof. vm_refl. Qed.
Lemma D_4434c : decode_any W_4434c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44350 : bv 32 := 0x00e60633.
Lemma F_44350 : fetch_word AsanUbsan.M.loaded_segments (0x44350 : word) = Some W_44350.
Proof. vm_refl. Qed.
Lemma D_44350 : decode_any W_44350 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44354 : bv 32 := 0xff85f713.
Lemma F_44354 : fetch_word AsanUbsan.M.loaded_segments (0x44354 : word) = Some W_44354.
Proof. vm_refl. Qed.
Lemma D_44354 : decode_any W_44354 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44358 : bv 32 := 0xff867793.
Lemma F_44358 : fetch_word AsanUbsan.M.loaded_segments (0x44358 : word) = Some W_44358.
Proof. vm_refl. Qed.
Lemma D_44358 : decode_any W_44358 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4435c : bv 32 := 0x00073703.
Lemma F_4435c : fetch_word AsanUbsan.M.loaded_segments (0x4435c : word) = Some W_4435c.
Proof. vm_refl. Qed.
Lemma D_4435c : decode_any W_4435c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44360 : bv 32 := 0x0007b783.
Lemma F_44360 : fetch_word AsanUbsan.M.loaded_segments (0x44360 : word) = Some W_44360.
Proof. vm_refl. Qed.
Lemma D_44360 : decode_any W_44360 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44364 : bv 32 := 0x00e7e733.
Lemma F_44364 : fetch_word AsanUbsan.M.loaded_segments (0x44364 : word) = Some W_44364.
Proof. vm_refl. Qed.
Lemma D_44364 : decode_any W_44364 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44368 : bv 32 := 0x0c071e63.
Lemma F_44368 : fetch_word AsanUbsan.M.loaded_segments (0x44368 : word) = Some W_44368.
Proof. vm_refl. Qed.
Lemma D_44368 : decode_any W_44368 = Some (Branch BC_NE 14 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4436c : bv 32 := 0x07010113.
Lemma F_4436c : fetch_word AsanUbsan.M.loaded_segments (0x4436c : word) = Some W_4436c.
Proof. vm_refl. Qed.
Lemma D_4436c : decode_any W_4436c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44370 : bv 32 := 0x7e813083.
Lemma F_44370 : fetch_word AsanUbsan.M.loaded_segments (0x44370 : word) = Some W_44370.
Proof. vm_refl. Qed.
Lemma D_44370 : decode_any W_44370 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44374 : bv 32 := 0x7e013403.
Lemma F_44374 : fetch_word AsanUbsan.M.loaded_segments (0x44374 : word) = Some W_44374.
Proof. vm_refl. Qed.
Lemma D_44374 : decode_any W_44374 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44378 : bv 32 := 0x7d813483.
Lemma F_44378 : fetch_word AsanUbsan.M.loaded_segments (0x44378 : word) = Some W_44378.
Proof. vm_refl. Qed.
Lemma D_44378 : decode_any W_44378 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4437c : bv 32 := 0x7d013903.
Lemma F_4437c : fetch_word AsanUbsan.M.loaded_segments (0x4437c : word) = Some W_4437c.
Proof. vm_refl. Qed.
Lemma D_4437c : decode_any W_4437c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44380 : bv 32 := 0x7c813983.
Lemma F_44380 : fetch_word AsanUbsan.M.loaded_segments (0x44380 : word) = Some W_44380.
Proof. vm_refl. Qed.
Lemma D_44380 : decode_any W_44380 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44384 : bv 32 := 0x7c013a03.
Lemma F_44384 : fetch_word AsanUbsan.M.loaded_segments (0x44384 : word) = Some W_44384.
Proof. vm_refl. Qed.
Lemma D_44384 : decode_any W_44384 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44388 : bv 32 := 0x7b813a83.
Lemma F_44388 : fetch_word AsanUbsan.M.loaded_segments (0x44388 : word) = Some W_44388.
Proof. vm_refl. Qed.
Lemma D_44388 : decode_any W_44388 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4438c : bv 32 := 0x7b013b03.
Lemma F_4438c : fetch_word AsanUbsan.M.loaded_segments (0x4438c : word) = Some W_4438c.
Proof. vm_refl. Qed.
Lemma D_4438c : decode_any W_4438c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44390 : bv 32 := 0x7f010113.
Lemma F_44390 : fetch_word AsanUbsan.M.loaded_segments (0x44390 : word) = Some W_44390.
Proof. vm_refl. Qed.
Lemma D_44390 : decode_any W_44390 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44394 : bv 32 := 0x00008067.
Lemma F_44394 : fetch_word AsanUbsan.M.loaded_segments (0x44394 : word) = Some W_44394.
Proof. vm_refl. Qed.
Lemma D_44394 : decode_any W_44394 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44398 : bv 32 := 0x00090513.
Lemma F_44398 : fetch_word AsanUbsan.M.loaded_segments (0x44398 : word) = Some W_44398.
Proof. vm_refl. Qed.
Lemma D_44398 : decode_any W_44398 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4439c : bv 32 := 0x07010113.
Lemma F_4439c : fetch_word AsanUbsan.M.loaded_segments (0x4439c : word) = Some W_4439c.
Proof. vm_refl. Qed.
Lemma D_4439c : decode_any W_4439c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443a0 : bv 32 := 0x7e813083.
Lemma F_443a0 : fetch_word AsanUbsan.M.loaded_segments (0x443a0 : word) = Some W_443a0.
Proof. vm_refl. Qed.
Lemma D_443a0 : decode_any W_443a0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443a4 : bv 32 := 0x7e013403.
Lemma F_443a4 : fetch_word AsanUbsan.M.loaded_segments (0x443a4 : word) = Some W_443a4.
Proof. vm_refl. Qed.
Lemma D_443a4 : decode_any W_443a4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443a8 : bv 32 := 0x7d813483.
Lemma F_443a8 : fetch_word AsanUbsan.M.loaded_segments (0x443a8 : word) = Some W_443a8.
Proof. vm_refl. Qed.
Lemma D_443a8 : decode_any W_443a8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443ac : bv 32 := 0x7d013903.
Lemma F_443ac : fetch_word AsanUbsan.M.loaded_segments (0x443ac : word) = Some W_443ac.
Proof. vm_refl. Qed.
Lemma D_443ac : decode_any W_443ac = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443b0 : bv 32 := 0x7c813983.
Lemma F_443b0 : fetch_word AsanUbsan.M.loaded_segments (0x443b0 : word) = Some W_443b0.
Proof. vm_refl. Qed.
Lemma D_443b0 : decode_any W_443b0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443b4 : bv 32 := 0x7c013a03.
Lemma F_443b4 : fetch_word AsanUbsan.M.loaded_segments (0x443b4 : word) = Some W_443b4.
Proof. vm_refl. Qed.
Lemma D_443b4 : decode_any W_443b4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443b8 : bv 32 := 0x7b813a83.
Lemma F_443b8 : fetch_word AsanUbsan.M.loaded_segments (0x443b8 : word) = Some W_443b8.
Proof. vm_refl. Qed.
Lemma D_443b8 : decode_any W_443b8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443bc : bv 32 := 0x7b013b03.
Lemma F_443bc : fetch_word AsanUbsan.M.loaded_segments (0x443bc : word) = Some W_443bc.
Proof. vm_refl. Qed.
Lemma D_443bc : decode_any W_443bc = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443c0 : bv 32 := 0x7f010113.
Lemma F_443c0 : fetch_word AsanUbsan.M.loaded_segments (0x443c0 : word) = Some W_443c0.
Proof. vm_refl. Qed.
Lemma D_443c0 : decode_any W_443c0 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443c4 : bv 32 := 0x73d2106f.
Lemma F_443c4 : fetch_word AsanUbsan.M.loaded_segments (0x443c4 : word) = Some W_443c4.
Proof. vm_refl. Qed.
Lemma D_443c4 : decode_any W_443c4 = Some (Jal 0 139068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443c8 : bv 32 := 0x80040593.
Lemma F_443c8 : fetch_word AsanUbsan.M.loaded_segments (0x443c8 : word) = Some W_443c8.
Proof. vm_refl. Qed.
Lemma D_443c8 : decode_any W_443c8 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443cc : bv 32 := 0xfb858593.
Lemma F_443cc : fetch_word AsanUbsan.M.loaded_segments (0x443cc : word) = Some W_443cc.
Proof. vm_refl. Qed.
Lemma D_443cc : decode_any W_443cc = Some (OpImm ALU_ADD 11 11 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443d0 : bv 32 := 0x80040613.
Lemma F_443d0 : fetch_word AsanUbsan.M.loaded_segments (0x443d0 : word) = Some W_443d0.
Proof. vm_refl. Qed.
Lemma D_443d0 : decode_any W_443d0 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443d4 : bv 32 := 0xfa860613.
Lemma F_443d4 : fetch_word AsanUbsan.M.loaded_segments (0x443d4 : word) = Some W_443d4.
Proof. vm_refl. Qed.
Lemma D_443d4 : decode_any W_443d4 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443d8 : bv 32 := 0x7ff60b13.
Lemma F_443d8 : fetch_word AsanUbsan.M.loaded_segments (0x443d8 : word) = Some W_443d8.
Proof. vm_refl. Qed.
Lemma D_443d8 : decode_any W_443d8 = Some (OpImm ALU_ADD 22 12 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443dc : bv 32 := 0x000b34a3.
Lemma F_443dc : fetch_word AsanUbsan.M.loaded_segments (0x443dc : word) = Some W_443dc.
Proof. vm_refl. Qed.
Lemma D_443dc : decode_any W_443dc = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443e0 : bv 32 := 0x00ba3023.
Lemma F_443e0 : fetch_word AsanUbsan.M.loaded_segments (0x443e0 : word) = Some W_443e0.
Proof. vm_refl. Qed.
Lemma D_443e0 : decode_any W_443e0 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443e4 : bv 32 := 0x000a3423.
Lemma F_443e4 : fetch_word AsanUbsan.M.loaded_segments (0x443e4 : word) = Some W_443e4.
Proof. vm_refl. Qed.
Lemma D_443e4 : decode_any W_443e4 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443e8 : bv 32 := 0x00050a93.
Lemma F_443e8 : fetch_word AsanUbsan.M.loaded_segments (0x443e8 : word) = Some W_443e8.
Proof. vm_refl. Qed.
Lemma D_443e8 : decode_any W_443e8 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443ec : bv 32 := 0x28c310ef.
Lemma F_443ec : fetch_word AsanUbsan.M.loaded_segments (0x443ec : word) = Some W_443ec.
Proof. vm_refl. Qed.
Lemma D_443ec : decode_any W_443ec = Some (Jal 1 201356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443f0 : bv 32 := 0x00050593.
Lemma F_443f0 : fetch_word AsanUbsan.M.loaded_segments (0x443f0 : word) = Some W_443f0.
Proof. vm_refl. Qed.
Lemma D_443f0 : decode_any W_443f0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443f4 : bv 32 := 0x0219c703.
Lemma F_443f4 : fetch_word AsanUbsan.M.loaded_segments (0x443f4 : word) = Some W_443f4.
Proof. vm_refl. Qed.
Lemma D_443f4 : decode_any W_443f4 = Some (Load SZ1 false 14 19 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443f8 : bv 32 := 0x008b34a3.
Lemma F_443f8 : fetch_word AsanUbsan.M.loaded_segments (0x443f8 : word) = Some W_443f8.
Proof. vm_refl. Qed.
Lemma D_443f8 : decode_any W_443f8 = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_443fc : bv 32 := 0x80040513.
Lemma F_443fc : fetch_word AsanUbsan.M.loaded_segments (0x443fc : word) = Some W_443fc.
Proof. vm_refl. Qed.
Lemma D_443fc : decode_any W_443fc = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44400 : bv 32 := 0xfa850513.
Lemma F_44400 : fetch_word AsanUbsan.M.loaded_segments (0x44400 : word) = Some W_44400.
Proof. vm_refl. Qed.
Lemma D_44400 : decode_any W_44400 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44404 : bv 32 := 0x0ff00793.
Lemma F_44404 : fetch_word AsanUbsan.M.loaded_segments (0x44404 : word) = Some W_44404.
Proof. vm_refl. Qed.
Lemma D_44404 : decode_any W_44404 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44408 : bv 32 := 0x00040613.
Lemma F_44408 : fetch_word AsanUbsan.M.loaded_segments (0x44408 : word) = Some W_44408.
Proof. vm_refl. Qed.
Lemma D_44408 : decode_any W_44408 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4440c : bv 32 := 0x00000693.
Lemma F_4440c : fetch_word AsanUbsan.M.loaded_segments (0x4440c : word) = Some W_4440c.
Proof. vm_refl. Qed.
Lemma D_4440c : decode_any W_4440c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44410 : bv 32 := 0x7b8180ef.
Lemma F_44410 : fetch_word AsanUbsan.M.loaded_segments (0x44410 : word) = Some W_44410.
Proof. vm_refl. Qed.
Lemma D_44410 : decode_any W_44410 = Some (Jal 1 100280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44414 : bv 32 := 0x80040613.
Lemma F_44414 : fetch_word AsanUbsan.M.loaded_segments (0x44414 : word) = Some W_44414.
Proof. vm_refl. Qed.
Lemma D_44414 : decode_any W_44414 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44418 : bv 32 := 0xfa860613.
Lemma F_44418 : fetch_word AsanUbsan.M.loaded_segments (0x44418 : word) = Some W_44418.
Proof. vm_refl. Qed.
Lemma D_44418 : decode_any W_44418 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4441c : bv 32 := 0x00090513.
Lemma F_4441c : fetch_word AsanUbsan.M.loaded_segments (0x4441c : word) = Some W_4441c.
Proof. vm_refl. Qed.
Lemma D_4441c : decode_any W_4441c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44420 : bv 32 := 0x00048593.
Lemma F_44420 : fetch_word AsanUbsan.M.loaded_segments (0x44420 : word) = Some W_44420.
Proof. vm_refl. Qed.
Lemma D_44420 : decode_any W_44420 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44424 : bv 32 := 0x55c150ef.
Lemma F_44424 : fetch_word AsanUbsan.M.loaded_segments (0x44424 : word) = Some W_44424.
Proof. vm_refl. Qed.
Lemma D_44424 : decode_any W_44424 = Some (Jal 1 87388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44428 : bv 32 := 0x000a8513.
Lemma F_44428 : fetch_word AsanUbsan.M.loaded_segments (0x44428 : word) = Some W_44428.
Proof. vm_refl. Qed.
Lemma D_44428 : decode_any W_44428 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4442c : bv 32 := 0x04000593.
Lemma F_4442c : fetch_word AsanUbsan.M.loaded_segments (0x4442c : word) = Some W_4442c.
Proof. vm_refl. Qed.
Lemma D_4442c : decode_any W_4442c = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44430 : bv 32 := 0xf0bae2e3.
Lemma F_44430 : fetch_word AsanUbsan.M.loaded_segments (0x44430 : word) = Some W_44430.
Proof. vm_refl. Qed.
Lemma D_44430 : decode_any W_44430 = Some (Branch BC_LTU 21 11 7940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44434 : bv 32 := 0x00050a93.
Lemma F_44434 : fetch_word AsanUbsan.M.loaded_segments (0x44434 : word) = Some W_44434.
Proof. vm_refl. Qed.
Lemma D_44434 : decode_any W_44434 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44438 : bv 32 := 0x04049263.
Lemma F_44438 : fetch_word AsanUbsan.M.loaded_segments (0x44438 : word) = Some W_44438.
Proof. vm_refl. Qed.
Lemma D_44438 : decode_any W_44438 = Some (Branch BC_NE 9 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4443c : bv 32 := 0xfff00513.
Lemma F_4443c : fetch_word AsanUbsan.M.loaded_segments (0x4443c : word) = Some W_4443c.
Proof. vm_refl. Qed.
Lemma D_4443c : decode_any W_4443c = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44440 : bv 32 := 0xf2dff06f.
Lemma F_44440 : fetch_word AsanUbsan.M.loaded_segments (0x44440 : word) = Some W_44440.
Proof. vm_refl. Qed.
Lemma D_44440 : decode_any W_44440 = Some (Jal 0 2096940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44444 : bv 32 := 0x00050a93.
Lemma F_44444 : fetch_word AsanUbsan.M.loaded_segments (0x44444 : word) = Some W_44444.
Proof. vm_refl. Qed.
Lemma D_44444 : decode_any W_44444 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44448 : bv 32 := 0x00060503.
Lemma F_44448 : fetch_word AsanUbsan.M.loaded_segments (0x44448 : word) = Some W_44448.
Proof. vm_refl. Qed.
Lemma D_44448 : decode_any W_44448 = Some (Load SZ1 true 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4444c : bv 32 := 0x0076f693.
Lemma F_4444c : fetch_word AsanUbsan.M.loaded_segments (0x4444c : word) = Some W_4444c.
Proof. vm_refl. Qed.
Lemma D_4444c : decode_any W_4444c = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44450 : bv 32 := 0x00a03733.
Lemma F_44450 : fetch_word AsanUbsan.M.loaded_segments (0x44450 : word) = Some W_44450.
Proof. vm_refl. Qed.
Lemma D_44450 : decode_any W_44450 = Some (Op ALU_SLTU 14 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44454 : bv 32 := 0x00a6a533.
Lemma F_44454 : fetch_word AsanUbsan.M.loaded_segments (0x44454 : word) = Some W_44454.
Proof. vm_refl. Qed.
Lemma D_44454 : decode_any W_44454 = Some (Op ALU_SLT 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44458 : bv 32 := 0x00154513.
Lemma F_44458 : fetch_word AsanUbsan.M.loaded_segments (0x44458 : word) = Some W_44458.
Proof. vm_refl. Qed.
Lemma D_44458 : decode_any W_44458 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4445c : bv 32 := 0x00a77533.
Lemma F_4445c : fetch_word AsanUbsan.M.loaded_segments (0x4445c : word) = Some W_4445c.
Proof. vm_refl. Qed.
Lemma D_4445c : decode_any W_4445c = Some (Op ALU_AND 10 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44460 : bv 32 := 0x00c5fa63.
Lemma F_44460 : fetch_word AsanUbsan.M.loaded_segments (0x44460 : word) = Some W_44460.
Proof. vm_refl. Qed.
Lemma D_44460 : decode_any W_44460 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44464 : bv 32 := 0x0005c683.
Lemma F_44464 : fetch_word AsanUbsan.M.loaded_segments (0x44464 : word) = Some W_44464.
Proof. vm_refl. Qed.
Lemma D_44464 : decode_any W_44464 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44468 : bv 32 := 0x00158593.
Lemma F_44468 : fetch_word AsanUbsan.M.loaded_segments (0x44468 : word) = Some W_44468.
Proof. vm_refl. Qed.
Lemma D_44468 : decode_any W_44468 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4446c : bv 32 := 0x00a6e533.
Lemma F_4446c : fetch_word AsanUbsan.M.loaded_segments (0x4446c : word) = Some W_4446c.
Proof. vm_refl. Qed.
Lemma D_4446c : decode_any W_4446c = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44470 : bv 32 := 0xfec59ae3.
Lemma F_44470 : fetch_word AsanUbsan.M.loaded_segments (0x44470 : word) = Some W_44470.
Proof. vm_refl. Qed.
Lemma D_44470 : decode_any W_44470 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44474 : bv 32 := 0x0ff57513.
Lemma F_44474 : fetch_word AsanUbsan.M.loaded_segments (0x44474 : word) = Some W_44474.
Proof. vm_refl. Qed.
Lemma D_44474 : decode_any W_44474 = Some (OpImm ALU_AND 10 10 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44478 : bv 32 := 0x0c050463.
Lemma F_44478 : fetch_word AsanUbsan.M.loaded_segments (0x44478 : word) = Some W_44478.
Proof. vm_refl. Qed.
Lemma D_44478 : decode_any W_44478 = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4447c : bv 32 := 0x00090513.
Lemma F_4447c : fetch_word AsanUbsan.M.loaded_segments (0x4447c : word) = Some W_4447c.
Proof. vm_refl. Qed.
Lemma D_4447c : decode_any W_4447c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44480 : bv 32 := 0x00048593.
Lemma F_44480 : fetch_word AsanUbsan.M.loaded_segments (0x44480 : word) = Some W_44480.
Proof. vm_refl. Qed.
Lemma D_44480 : decode_any W_44480 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44484 : bv 32 := 0x518120ef.
Lemma F_44484 : fetch_word AsanUbsan.M.loaded_segments (0x44484 : word) = Some W_44484.
Proof. vm_refl. Qed.
Lemma D_44484 : decode_any W_44484 = Some (Jal 1 75032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44488 : bv 32 := 0x0a050c63.
Lemma F_44488 : fetch_word AsanUbsan.M.loaded_segments (0x44488 : word) = Some W_44488.
Proof. vm_refl. Qed.
Lemma D_44488 : decode_any W_44488 = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4448c : bv 32 := 0x00050913.
Lemma F_4448c : fetch_word AsanUbsan.M.loaded_segments (0x4448c : word) = Some W_4448c.
Proof. vm_refl. Qed.
Lemma D_4448c : decode_any W_4448c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44490 : bv 32 := 0xfffd3517.
Lemma F_44490 : fetch_word AsanUbsan.M.loaded_segments (0x44490 : word) = Some W_44490.
Proof. vm_refl. Qed.
Lemma D_44490 : decode_any W_44490 = Some (Auipc 10 1048531, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44494 : bv 32 := 0x95350513.
Lemma F_44494 : fetch_word AsanUbsan.M.loaded_segments (0x44494 : word) = Some W_44494.
Proof. vm_refl. Qed.
Lemma D_44494 : decode_any W_44494 = Some (OpImm ALU_ADD 10 10 2387, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44498 : bv 32 := 0x6dc190ef.
Lemma F_44498 : fetch_word AsanUbsan.M.loaded_segments (0x44498 : word) = Some W_44498.
Proof. vm_refl. Qed.
Lemma D_44498 : decode_any W_44498 = Some (Jal 1 104156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4449c : bv 32 := 0x0a051263.
Lemma F_4449c : fetch_word AsanUbsan.M.loaded_segments (0x4449c : word) = Some W_4449c.
Proof. vm_refl. Qed.
Lemma D_4449c : decode_any W_4449c = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444a0 : bv 32 := 0x73c190ef.
Lemma F_444a0 : fetch_word AsanUbsan.M.loaded_segments (0x444a0 : word) = Some W_444a0.
Proof. vm_refl. Qed.
Lemma D_444a0 : decode_any W_444a0 = Some (Jal 1 104252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444a4 : bv 32 := 0x06050263.
Lemma F_444a4 : fetch_word AsanUbsan.M.loaded_segments (0x444a4 : word) = Some W_444a4.
Proof. vm_refl. Qed.
Lemma D_444a4 : decode_any W_444a4 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444a8 : bv 32 := 0x80040513.
Lemma F_444a8 : fetch_word AsanUbsan.M.loaded_segments (0x444a8 : word) = Some W_444a8.
Proof. vm_refl. Qed.
Lemma D_444a8 : decode_any W_444a8 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444ac : bv 32 := 0xfb850513.
Lemma F_444ac : fetch_word AsanUbsan.M.loaded_segments (0x444ac : word) = Some W_444ac.
Proof. vm_refl. Qed.
Lemma D_444ac : decode_any W_444ac = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444b0 : bv 32 := 0x80040593.
Lemma F_444b0 : fetch_word AsanUbsan.M.loaded_segments (0x444b0 : word) = Some W_444b0.
Proof. vm_refl. Qed.
Lemma D_444b0 : decode_any W_444b0 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444b4 : bv 32 := 0xfa858593.
Lemma F_444b4 : fetch_word AsanUbsan.M.loaded_segments (0x444b4 : word) = Some W_444b4.
Proof. vm_refl. Qed.
Lemma D_444b4 : decode_any W_444b4 = Some (OpImm ALU_ADD 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444b8 : bv 32 := 0x7ff58b13.
Lemma F_444b8 : fetch_word AsanUbsan.M.loaded_segments (0x444b8 : word) = Some W_444b8.
Proof. vm_refl. Qed.
Lemma D_444b8 : decode_any W_444b8 = Some (OpImm ALU_ADD 22 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444bc : bv 32 := 0x000b34a3.
Lemma F_444bc : fetch_word AsanUbsan.M.loaded_segments (0x444bc : word) = Some W_444bc.
Proof. vm_refl. Qed.
Lemma D_444bc : decode_any W_444bc = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444c0 : bv 32 := 0x00aa3023.
Lemma F_444c0 : fetch_word AsanUbsan.M.loaded_segments (0x444c0 : word) = Some W_444c0.
Proof. vm_refl. Qed.
Lemma D_444c0 : decode_any W_444c0 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444c4 : bv 32 := 0x000a3423.
Lemma F_444c4 : fetch_word AsanUbsan.M.loaded_segments (0x444c4 : word) = Some W_444c4.
Proof. vm_refl. Qed.
Lemma D_444c4 : decode_any W_444c4 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444c8 : bv 32 := 0x1b0310ef.
Lemma F_444c8 : fetch_word AsanUbsan.M.loaded_segments (0x444c8 : word) = Some W_444c8.
Proof. vm_refl. Qed.
Lemma D_444c8 : decode_any W_444c8 = Some (Jal 1 201136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444cc : bv 32 := 0x00050593.
Lemma F_444cc : fetch_word AsanUbsan.M.loaded_segments (0x444cc : word) = Some W_444cc.
Proof. vm_refl. Qed.
Lemma D_444cc : decode_any W_444cc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444d0 : bv 32 := 0x0219c703.
Lemma F_444d0 : fetch_word AsanUbsan.M.loaded_segments (0x444d0 : word) = Some W_444d0.
Proof. vm_refl. Qed.
Lemma D_444d0 : decode_any W_444d0 = Some (Load SZ1 false 14 19 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444d4 : bv 32 := 0x008b34a3.
Lemma F_444d4 : fetch_word AsanUbsan.M.loaded_segments (0x444d4 : word) = Some W_444d4.
Proof. vm_refl. Qed.
Lemma D_444d4 : decode_any W_444d4 = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444d8 : bv 32 := 0x80040513.
Lemma F_444d8 : fetch_word AsanUbsan.M.loaded_segments (0x444d8 : word) = Some W_444d8.
Proof. vm_refl. Qed.
Lemma D_444d8 : decode_any W_444d8 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444dc : bv 32 := 0xfa850513.
Lemma F_444dc : fetch_word AsanUbsan.M.loaded_segments (0x444dc : word) = Some W_444dc.
Proof. vm_refl. Qed.
Lemma D_444dc : decode_any W_444dc = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444e0 : bv 32 := 0x0ff00793.
Lemma F_444e0 : fetch_word AsanUbsan.M.loaded_segments (0x444e0 : word) = Some W_444e0.
Proof. vm_refl. Qed.
Lemma D_444e0 : decode_any W_444e0 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444e4 : bv 32 := 0x00040613.
Lemma F_444e4 : fetch_word AsanUbsan.M.loaded_segments (0x444e4 : word) = Some W_444e4.
Proof. vm_refl. Qed.
Lemma D_444e4 : decode_any W_444e4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444e8 : bv 32 := 0x00000693.
Lemma F_444e8 : fetch_word AsanUbsan.M.loaded_segments (0x444e8 : word) = Some W_444e8.
Proof. vm_refl. Qed.
Lemma D_444e8 : decode_any W_444e8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444ec : bv 32 := 0x6dc180ef.
Lemma F_444ec : fetch_word AsanUbsan.M.loaded_segments (0x444ec : word) = Some W_444ec.
Proof. vm_refl. Qed.
Lemma D_444ec : decode_any W_444ec = Some (Jal 1 100060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444f0 : bv 32 := 0x80040513.
Lemma F_444f0 : fetch_word AsanUbsan.M.loaded_segments (0x444f0 : word) = Some W_444f0.
Proof. vm_refl. Qed.
Lemma D_444f0 : decode_any W_444f0 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444f4 : bv 32 := 0xfa850513.
Lemma F_444f4 : fetch_word AsanUbsan.M.loaded_segments (0x444f4 : word) = Some W_444f4.
Proof. vm_refl. Qed.
Lemma D_444f4 : decode_any W_444f4 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444f8 : bv 32 := 0x1ed190ef.
Lemma F_444f8 : fetch_word AsanUbsan.M.loaded_segments (0x444f8 : word) = Some W_444f8.
Proof. vm_refl. Qed.
Lemma D_444f8 : decode_any W_444f8 = Some (Jal 1 104940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_444fc : bv 32 := 0x00040993.
Lemma F_444fc : fetch_word AsanUbsan.M.loaded_segments (0x444fc : word) = Some W_444fc.
Proof. vm_refl. Qed.
Lemma D_444fc : decode_any W_444fc = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44500 : bv 32 := 0x00050663.
Lemma F_44500 : fetch_word AsanUbsan.M.loaded_segments (0x44500 : word) = Some W_44500.
Proof. vm_refl. Qed.
Lemma D_44500 : decode_any W_44500 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44504 : bv 32 := 0x03c0006f.
Lemma F_44504 : fetch_word AsanUbsan.M.loaded_segments (0x44504 : word) = Some W_44504.
Proof. vm_refl. Qed.
Lemma D_44504 : decode_any W_44504 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44508 : bv 32 := 0x00040993.
Lemma F_44508 : fetch_word AsanUbsan.M.loaded_segments (0x44508 : word) = Some W_44508.
Proof. vm_refl. Qed.
Lemma D_44508 : decode_any W_44508 = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4450c : bv 32 := 0x16c310ef.
Lemma F_4450c : fetch_word AsanUbsan.M.loaded_segments (0x4450c : word) = Some W_4450c.
Proof. vm_refl. Qed.
Lemma D_4450c : decode_any W_4450c = Some (Jal 1 201068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44510 : bv 32 := 0xfffcc597.
Lemma F_44510 : fetch_word AsanUbsan.M.loaded_segments (0x44510 : word) = Some W_44510.
Proof. vm_refl. Qed.
Lemma D_44510 : decode_any W_44510 = Some (Auipc 11 1048524, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44514 : bv 32 := 0xee85b583.
Lemma F_44514 : fetch_word AsanUbsan.M.loaded_segments (0x44514 : word) = Some W_44514.
Proof. vm_refl. Qed.
Lemma D_44514 : decode_any W_44514 = Some (Load SZ8 true 11 11 3816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44518 : bv 32 := 0x00ba3023.
Lemma F_44518 : fetch_word AsanUbsan.M.loaded_segments (0x44518 : word) = Some W_44518.
Proof. vm_refl. Qed.
Lemma D_44518 : decode_any W_44518 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4451c : bv 32 := 0x80040613.
Lemma F_4451c : fetch_word AsanUbsan.M.loaded_segments (0x4451c : word) = Some W_4451c.
Proof. vm_refl. Qed.
Lemma D_4451c : decode_any W_4451c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44520 : bv 32 := 0xfa860613.
Lemma F_44520 : fetch_word AsanUbsan.M.loaded_segments (0x44520 : word) = Some W_44520.
Proof. vm_refl. Qed.
Lemma D_44520 : decode_any W_44520 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44524 : bv 32 := 0x00098593.
Lemma F_44524 : fetch_word AsanUbsan.M.loaded_segments (0x44524 : word) = Some W_44524.
Proof. vm_refl. Qed.
Lemma D_44524 : decode_any W_44524 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44528 : bv 32 := 0x00090693.
Lemma F_44528 : fetch_word AsanUbsan.M.loaded_segments (0x44528 : word) = Some W_44528.
Proof. vm_refl. Qed.
Lemma D_44528 : decode_any W_44528 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4452c : bv 32 := 0x00000713.
Lemma F_4452c : fetch_word AsanUbsan.M.loaded_segments (0x4452c : word) = Some W_4452c.
Proof. vm_refl. Qed.
Lemma D_4452c : decode_any W_4452c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44530 : bv 32 := 0x00048793.
Lemma F_44530 : fetch_word AsanUbsan.M.loaded_segments (0x44530 : word) = Some W_44530.
Proof. vm_refl. Qed.
Lemma D_44530 : decode_any W_44530 = Some (OpImm ALU_ADD 15 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44534 : bv 32 := 0x00000813.
Lemma F_44534 : fetch_word AsanUbsan.M.loaded_segments (0x44534 : word) = Some W_44534.
Proof. vm_refl. Qed.
Lemma D_44534 : decode_any W_44534 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44538 : bv 32 := 0x00000893.
Lemma F_44538 : fetch_word AsanUbsan.M.loaded_segments (0x44538 : word) = Some W_44538.
Proof. vm_refl. Qed.
Lemma D_44538 : decode_any W_44538 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4453c : bv 32 := 0x19d150ef.
Lemma F_4453c : fetch_word AsanUbsan.M.loaded_segments (0x4453c : word) = Some W_4453c.
Proof. vm_refl. Qed.
Lemma D_4453c : decode_any W_4453c = Some (Jal 1 88476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44540 : bv 32 := 0x000a8513.
Lemma F_44540 : fetch_word AsanUbsan.M.loaded_segments (0x44540 : word) = Some W_44540.
Proof. vm_refl. Qed.
Lemma D_44540 : decode_any W_44540 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44544 : bv 32 := 0xe29ff06f.
Lemma F_44544 : fetch_word AsanUbsan.M.loaded_segments (0x44544 : word) = Some W_44544.
Proof. vm_refl. Qed.
Lemma D_44544 : decode_any W_44544 = Some (Jal 0 2096680, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_5af20 : bv 32 := 0x00058517.
Lemma F_5af20 : fetch_word AsanUbsan.M.loaded_segments (0x5af20 : word) = Some W_5af20.
Proof. vm_refl. Qed.
Lemma D_5af20 : decode_any W_5af20 = Some (Auipc 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af24 : bv 32 := 0x97850503.
Lemma F_5af24 : fetch_word AsanUbsan.M.loaded_segments (0x5af24 : word) = Some W_5af24.
Proof. vm_refl. Qed.
Lemma D_5af24 : decode_any W_5af24 = Some (Load SZ1 true 10 10 2424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af28 : bv 32 := 0x0230000f.
Lemma F_5af28 : fetch_word AsanUbsan.M.loaded_segments (0x5af28 : word) = Some W_5af28.
Proof. vm_refl. Qed.
Lemma D_5af28 : decode_any W_5af28 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af2c : bv 32 := 0xfff50513.
Lemma F_5af2c : fetch_word AsanUbsan.M.loaded_segments (0x5af2c : word) = Some W_5af2c.
Proof. vm_refl. Qed.
Lemma D_5af2c : decode_any W_5af2c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af30 : bv 32 := 0x00153513.
Lemma F_5af30 : fetch_word AsanUbsan.M.loaded_segments (0x5af30 : word) = Some W_5af30.
Proof. vm_refl. Qed.
Lemma D_5af30 : decode_any W_5af30 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af34 : bv 32 := 0x00008067.
Lemma F_5af34 : fetch_word AsanUbsan.M.loaded_segments (0x5af34 : word) = Some W_5af34.
Proof. vm_refl. Qed.
Lemma D_5af34 : decode_any W_5af34 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
