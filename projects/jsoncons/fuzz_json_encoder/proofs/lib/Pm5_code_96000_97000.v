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
Definition W_96300 : bv 32 := 0xfd010113.
Lemma F_96300 : fetch_word AsanUbsan.M.loaded_segments (0x96348 : word) = Some W_96300.
Proof. vm_refl. Qed.
Lemma D_96300 : decode_any W_96300 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96304 : bv 32 := 0x02113423.
Lemma F_96304 : fetch_word AsanUbsan.M.loaded_segments (0x9634c : word) = Some W_96304.
Proof. vm_refl. Qed.
Lemma D_96304 : decode_any W_96304 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96308 : bv 32 := 0x02813023.
Lemma F_96308 : fetch_word AsanUbsan.M.loaded_segments (0x96350 : word) = Some W_96308.
Proof. vm_refl. Qed.
Lemma D_96308 : decode_any W_96308 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9630c : bv 32 := 0x00913c23.
Lemma F_9630c : fetch_word AsanUbsan.M.loaded_segments (0x96354 : word) = Some W_9630c.
Proof. vm_refl. Qed.
Lemma D_9630c : decode_any W_9630c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96310 : bv 32 := 0x01213823.
Lemma F_96310 : fetch_word AsanUbsan.M.loaded_segments (0x96358 : word) = Some W_96310.
Proof. vm_refl. Qed.
Lemma D_96310 : decode_any W_96310 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96314 : bv 32 := 0x02050e63.
Lemma F_96314 : fetch_word AsanUbsan.M.loaded_segments (0x9635c : word) = Some W_96314.
Proof. vm_refl. Qed.
Lemma D_96314 : decode_any W_96314 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96318 : bv 32 := 0x00058413.
Lemma F_96318 : fetch_word AsanUbsan.M.loaded_segments (0x96360 : word) = Some W_96318.
Proof. vm_refl. Qed.
Lemma D_96318 : decode_any W_96318 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9631c : bv 32 := 0x02058a63.
Lemma F_9631c : fetch_word AsanUbsan.M.loaded_segments (0x96364 : word) = Some W_9631c.
Proof. vm_refl. Qed.
Lemma D_9631c : decode_any W_9631c = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96320 : bv 32 := 0x00060493.
Lemma F_96320 : fetch_word AsanUbsan.M.loaded_segments (0x96368 : word) = Some W_96320.
Proof. vm_refl. Qed.
Lemma D_96320 : decode_any W_96320 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96324 : bv 32 := 0x00050913.
Lemma F_96324 : fetch_word AsanUbsan.M.loaded_segments (0x9636c : word) = Some W_96324.
Proof. vm_refl. Qed.
Lemma D_96324 : decode_any W_96324 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96328 : bv 32 := 0x00040593.
Lemma F_96328 : fetch_word AsanUbsan.M.loaded_segments (0x96370 : word) = Some W_96328.
Proof. vm_refl. Qed.
Lemma D_96328 : decode_any W_96328 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9632c : bv 32 := 0xf90fe0ef.
Lemma F_9632c : fetch_word AsanUbsan.M.loaded_segments (0x96374 : word) = Some W_9632c.
Proof. vm_refl. Qed.
Lemma D_9632c : decode_any W_9632c = Some (Jal 1 2090896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96330 : bv 32 := 0xaaaab5b7.
Lemma F_96330 : fetch_word AsanUbsan.M.loaded_segments (0x96378 : word) = Some W_96330.
Proof. vm_refl. Qed.
Lemma D_96330 : decode_any W_96330 = Some (Lui 11 699051, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96334 : bv 32 := 0xaaa58593.
Lemma F_96334 : fetch_word AsanUbsan.M.loaded_segments (0x9637c : word) = Some W_96334.
Proof. vm_refl. Qed.
Lemma D_96334 : decode_any W_96334 = Some (OpImm ALU_ADD 11 11 2730, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96338 : bv 32 := 0x00b12623.
Lemma F_96338 : fetch_word AsanUbsan.M.loaded_segments (0x96380 : word) = Some W_96338.
Proof. vm_refl. Qed.
Lemma D_96338 : decode_any W_96338 = Some (Store SZ4 2 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9633c : bv 32 := 0x00c10593.
Lemma F_9633c : fetch_word AsanUbsan.M.loaded_segments (0x96384 : word) = Some W_9633c.
Proof. vm_refl. Qed.
Lemma D_9633c : decode_any W_9633c = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96340 : bv 32 := 0xf50fe0ef.
Lemma F_96340 : fetch_word AsanUbsan.M.loaded_segments (0x96388 : word) = Some W_96340.
Proof. vm_refl. Qed.
Lemma D_96340 : decode_any W_96340 = Some (Jal 1 2090832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96344 : bv 32 := 0x02051263.
Lemma F_96344 : fetch_word AsanUbsan.M.loaded_segments (0x9638c : word) = Some W_96344.
Proof. vm_refl. Qed.
Lemma D_96344 : decode_any W_96344 = Some (Branch BC_NE 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96348 : bv 32 := 0x00040513.
Lemma F_96348 : fetch_word AsanUbsan.M.loaded_segments (0x96390 : word) = Some W_96348.
Proof. vm_refl. Qed.
Lemma D_96348 : decode_any W_96348 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9634c : bv 32 := 0xe70fa0ef.
Lemma F_9634c : fetch_word AsanUbsan.M.loaded_segments (0x96394 : word) = Some W_9634c.
Proof. vm_refl. Qed.
Lemma D_9634c : decode_any W_9634c = Some (Jal 1 2074224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96350 : bv 32 := 0x02813083.
Lemma F_96350 : fetch_word AsanUbsan.M.loaded_segments (0x96398 : word) = Some W_96350.
Proof. vm_refl. Qed.
Lemma D_96350 : decode_any W_96350 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96354 : bv 32 := 0x02013403.
Lemma F_96354 : fetch_word AsanUbsan.M.loaded_segments (0x9639c : word) = Some W_96354.
Proof. vm_refl. Qed.
Lemma D_96354 : decode_any W_96354 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96358 : bv 32 := 0x01813483.
Lemma F_96358 : fetch_word AsanUbsan.M.loaded_segments (0x963a0 : word) = Some W_96358.
Proof. vm_refl. Qed.
Lemma D_96358 : decode_any W_96358 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9635c : bv 32 := 0x01013903.
Lemma F_9635c : fetch_word AsanUbsan.M.loaded_segments (0x963a4 : word) = Some W_9635c.
Proof. vm_refl. Qed.
Lemma D_9635c : decode_any W_9635c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96360 : bv 32 := 0x03010113.
Lemma F_96360 : fetch_word AsanUbsan.M.loaded_segments (0x963a8 : word) = Some W_96360.
Proof. vm_refl. Qed.
Lemma D_96360 : decode_any W_96360 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96364 : bv 32 := 0x00008067.
Lemma F_96364 : fetch_word AsanUbsan.M.loaded_segments (0x963ac : word) = Some W_96364.
Proof. vm_refl. Qed.
Lemma D_96364 : decode_any W_96364 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9637c : bv 32 := 0xfd010113.
Lemma F_9637c : fetch_word AsanUbsan.M.loaded_segments (0x963c4 : word) = Some W_9637c.
Proof. vm_refl. Qed.
Lemma D_9637c : decode_any W_9637c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96380 : bv 32 := 0x02113423.
Lemma F_96380 : fetch_word AsanUbsan.M.loaded_segments (0x963c8 : word) = Some W_96380.
Proof. vm_refl. Qed.
Lemma D_96380 : decode_any W_96380 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96384 : bv 32 := 0x02813023.
Lemma F_96384 : fetch_word AsanUbsan.M.loaded_segments (0x963cc : word) = Some W_96384.
Proof. vm_refl. Qed.
Lemma D_96384 : decode_any W_96384 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96388 : bv 32 := 0x00913c23.
Lemma F_96388 : fetch_word AsanUbsan.M.loaded_segments (0x963d0 : word) = Some W_96388.
Proof. vm_refl. Qed.
Lemma D_96388 : decode_any W_96388 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9638c : bv 32 := 0x01213823.
Lemma F_9638c : fetch_word AsanUbsan.M.loaded_segments (0x963d4 : word) = Some W_9638c.
Proof. vm_refl. Qed.
Lemma D_9638c : decode_any W_9638c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96390 : bv 32 := 0x00058413.
Lemma F_96390 : fetch_word AsanUbsan.M.loaded_segments (0x963d8 : word) = Some W_96390.
Proof. vm_refl. Qed.
Lemma D_96390 : decode_any W_96390 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96394 : bv 32 := 0x000ce597.
Lemma F_96394 : fetch_word AsanUbsan.M.loaded_segments (0x963dc : word) = Some W_96394.
Proof. vm_refl. Qed.
Lemma D_96394 : decode_any W_96394 = Some (Auipc 11 206, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96398 : bv 32 := 0x11c5b903.
Lemma F_96398 : fetch_word AsanUbsan.M.loaded_segments (0x963e0 : word) = Some W_96398.
Proof. vm_refl. Qed.
Lemma D_96398 : decode_any W_96398 = Some (Load SZ8 true 18 11 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9639c : bv 32 := 0x00093583.
Lemma F_9639c : fetch_word AsanUbsan.M.loaded_segments (0x963e4 : word) = Some W_9639c.
Proof. vm_refl. Qed.
Lemma D_9639c : decode_any W_9639c = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963a0 : bv 32 := 0x00050493.
Lemma F_963a0 : fetch_word AsanUbsan.M.loaded_segments (0x963e8 : word) = Some W_963a0.
Proof. vm_refl. Qed.
Lemma D_963a0 : decode_any W_963a0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963a4 : bv 32 := 0x00059863.
Lemma F_963a4 : fetch_word AsanUbsan.M.loaded_segments (0x963ec : word) = Some W_963a4.
Proof. vm_refl. Qed.
Lemma D_963a4 : decode_any W_963a4 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963b4 : bv 32 := 0xfff58513.
Lemma F_963b4 : fetch_word AsanUbsan.M.loaded_segments (0x963fc : word) = Some W_963b4.
Proof. vm_refl. Qed.
Lemma D_963b4 : decode_any W_963b4 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963b8 : bv 32 := 0x00a5f533.
Lemma F_963b8 : fetch_word AsanUbsan.M.loaded_segments (0x96400 : word) = Some W_963b8.
Proof. vm_refl. Qed.
Lemma D_963b8 : decode_any W_963b8 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963bc : bv 32 := 0x08051a63.
Lemma F_963bc : fetch_word AsanUbsan.M.loaded_segments (0x96404 : word) = Some W_963bc.
Proof. vm_refl. Qed.
Lemma D_963bc : decode_any W_963bc = Some (Branch BC_NE 10 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963c0 : bv 32 := 0x00b484b3.
Lemma F_963c0 : fetch_word AsanUbsan.M.loaded_segments (0x96408 : word) = Some W_963c0.
Proof. vm_refl. Qed.
Lemma D_963c0 : decode_any W_963c0 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963c4 : bv 32 := 0x40b00533.
Lemma F_963c4 : fetch_word AsanUbsan.M.loaded_segments (0x9640c : word) = Some W_963c4.
Proof. vm_refl. Qed.
Lemma D_963c4 : decode_any W_963c4 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963c8 : bv 32 := 0xfff48493.
Lemma F_963c8 : fetch_word AsanUbsan.M.loaded_segments (0x96410 : word) = Some W_963c8.
Proof. vm_refl. Qed.
Lemma D_963c8 : decode_any W_963c8 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963cc : bv 32 := 0x00a4f4b3.
Lemma F_963cc : fetch_word AsanUbsan.M.loaded_segments (0x96414 : word) = Some W_963cc.
Proof. vm_refl. Qed.
Lemma D_963cc : decode_any W_963cc = Some (Op ALU_AND 9 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963d0 : bv 32 := 0x02200513.
Lemma F_963d0 : fetch_word AsanUbsan.M.loaded_segments (0x96418 : word) = Some W_963d0.
Proof. vm_refl. Qed.
Lemma D_963d0 : decode_any W_963d0 = Some (OpImm ALU_ADD 10 0 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963d4 : bv 32 := 0x00a12623.
Lemma F_963d4 : fetch_word AsanUbsan.M.loaded_segments (0x9641c : word) = Some W_963d4.
Proof. vm_refl. Qed.
Lemma D_963d4 : decode_any W_963d4 = Some (Store SZ4 2 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963d8 : bv 32 := 0x00c10613.
Lemma F_963d8 : fetch_word AsanUbsan.M.loaded_segments (0x96420 : word) = Some W_963d8.
Proof. vm_refl. Qed.
Lemma D_963d8 : decode_any W_963d8 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963dc : bv 32 := 0x00040513.
Lemma F_963dc : fetch_word AsanUbsan.M.loaded_segments (0x96424 : word) = Some W_963dc.
Proof. vm_refl. Qed.
Lemma D_963dc : decode_any W_963dc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963e0 : bv 32 := 0x00048593.
Lemma F_963e0 : fetch_word AsanUbsan.M.loaded_segments (0x96428 : word) = Some W_963e0.
Proof. vm_refl. Qed.
Lemma D_963e0 : decode_any W_963e0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963e4 : bv 32 := 0x279000ef.
Lemma F_963e4 : fetch_word AsanUbsan.M.loaded_segments (0x9642c : word) = Some W_963e4.
Proof. vm_refl. Qed.
Lemma D_963e4 : decode_any W_963e4 = Some (Jal 1 2680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963e8 : bv 32 := 0x00c12683.
Lemma F_963e8 : fetch_word AsanUbsan.M.loaded_segments (0x96430 : word) = Some W_963e8.
Proof. vm_refl. Qed.
Lemma D_963e8 : decode_any W_963e8 = Some (Load SZ4 true 13 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963ec : bv 32 := 0x00050713.
Lemma F_963ec : fetch_word AsanUbsan.M.loaded_segments (0x96434 : word) = Some W_963ec.
Proof. vm_refl. Qed.
Lemma D_963ec : decode_any W_963ec = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963f0 : bv 32 := 0x00300613.
Lemma F_963f0 : fetch_word AsanUbsan.M.loaded_segments (0x96438 : word) = Some W_963f0.
Proof. vm_refl. Qed.
Lemma D_963f0 : decode_any W_963f0 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963f4 : bv 32 := 0x00000513.
Lemma F_963f4 : fetch_word AsanUbsan.M.loaded_segments (0x9643c : word) = Some W_963f4.
Proof. vm_refl. Qed.
Lemma D_963f4 : decode_any W_963f4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963f8 : bv 32 := 0x00048593.
Lemma F_963f8 : fetch_word AsanUbsan.M.loaded_segments (0x96440 : word) = Some W_963f8.
Proof. vm_refl. Qed.
Lemma D_963f8 : decode_any W_963f8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963fc : bv 32 := 0x00000793.
Lemma F_963fc : fetch_word AsanUbsan.M.loaded_segments (0x96444 : word) = Some W_963fc.
Proof. vm_refl. Qed.
Lemma D_963fc : decode_any W_963fc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96400 : bv 32 := 0xeb0fe0ef.
Lemma F_96400 : fetch_word AsanUbsan.M.loaded_segments (0x96448 : word) = Some W_96400.
Proof. vm_refl. Qed.
Lemma D_96400 : decode_any W_96400 = Some (Jal 1 2090672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96404 : bv 32 := 0x00050913.
Lemma F_96404 : fetch_word AsanUbsan.M.loaded_segments (0x9644c : word) = Some W_96404.
Proof. vm_refl. Qed.
Lemma D_96404 : decode_any W_96404 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96408 : bv 32 := 0x00000593.
Lemma F_96408 : fetch_word AsanUbsan.M.loaded_segments (0x96450 : word) = Some W_96408.
Proof. vm_refl. Qed.
Lemma D_96408 : decode_any W_96408 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9640c : bv 32 := 0xe84fe0ef.
Lemma F_9640c : fetch_word AsanUbsan.M.loaded_segments (0x96454 : word) = Some W_9640c.
Proof. vm_refl. Qed.
Lemma D_9640c : decode_any W_9640c = Some (Jal 1 2090628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96410 : bv 32 := 0xaaaab537.
Lemma F_96410 : fetch_word AsanUbsan.M.loaded_segments (0x96458 : word) = Some W_96410.
Proof. vm_refl. Qed.
Lemma D_96410 : decode_any W_96410 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96414 : bv 32 := 0xaaa50513.
Lemma F_96414 : fetch_word AsanUbsan.M.loaded_segments (0x9645c : word) = Some W_96414.
Proof. vm_refl. Qed.
Lemma D_96414 : decode_any W_96414 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96418 : bv 32 := 0x00a12423.
Lemma F_96418 : fetch_word AsanUbsan.M.loaded_segments (0x96460 : word) = Some W_96418.
Proof. vm_refl. Qed.
Lemma D_96418 : decode_any W_96418 = Some (Store SZ4 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9641c : bv 32 := 0x00810593.
Lemma F_9641c : fetch_word AsanUbsan.M.loaded_segments (0x96464 : word) = Some W_9641c.
Proof. vm_refl. Qed.
Lemma D_9641c : decode_any W_9641c = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96420 : bv 32 := 0x00090513.
Lemma F_96420 : fetch_word AsanUbsan.M.loaded_segments (0x96468 : word) = Some W_96420.
Proof. vm_refl. Qed.
Lemma D_96420 : decode_any W_96420 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96424 : bv 32 := 0xe6cfe0ef.
Lemma F_96424 : fetch_word AsanUbsan.M.loaded_segments (0x9646c : word) = Some W_96424.
Proof. vm_refl. Qed.
Lemma D_96424 : decode_any W_96424 = Some (Jal 1 2090604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96428 : bv 32 := 0x02051c63.
Lemma F_96428 : fetch_word AsanUbsan.M.loaded_segments (0x96470 : word) = Some W_96428.
Proof. vm_refl. Qed.
Lemma D_96428 : decode_any W_96428 = Some (Branch BC_NE 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9642c : bv 32 := 0x00048513.
Lemma F_9642c : fetch_word AsanUbsan.M.loaded_segments (0x96474 : word) = Some W_9642c.
Proof. vm_refl. Qed.
Lemma D_9642c : decode_any W_9642c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96430 : bv 32 := 0xd48fa0ef.
Lemma F_96430 : fetch_word AsanUbsan.M.loaded_segments (0x96478 : word) = Some W_96430.
Proof. vm_refl. Qed.
Lemma D_96430 : decode_any W_96430 = Some (Jal 1 2073928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96434 : bv 32 := 0x00090513.
Lemma F_96434 : fetch_word AsanUbsan.M.loaded_segments (0x9647c : word) = Some W_96434.
Proof. vm_refl. Qed.
Lemma D_96434 : decode_any W_96434 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96438 : bv 32 := 0x02813083.
Lemma F_96438 : fetch_word AsanUbsan.M.loaded_segments (0x96480 : word) = Some W_96438.
Proof. vm_refl. Qed.
Lemma D_96438 : decode_any W_96438 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9643c : bv 32 := 0x02013403.
Lemma F_9643c : fetch_word AsanUbsan.M.loaded_segments (0x96484 : word) = Some W_9643c.
Proof. vm_refl. Qed.
Lemma D_9643c : decode_any W_9643c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96440 : bv 32 := 0x01813483.
Lemma F_96440 : fetch_word AsanUbsan.M.loaded_segments (0x96488 : word) = Some W_96440.
Proof. vm_refl. Qed.
Lemma D_96440 : decode_any W_96440 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96444 : bv 32 := 0x01013903.
Lemma F_96444 : fetch_word AsanUbsan.M.loaded_segments (0x9648c : word) = Some W_96444.
Proof. vm_refl. Qed.
Lemma D_96444 : decode_any W_96444 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96448 : bv 32 := 0x03010113.
Lemma F_96448 : fetch_word AsanUbsan.M.loaded_segments (0x96490 : word) = Some W_96448.
Proof. vm_refl. Qed.
Lemma D_96448 : decode_any W_96448 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9644c : bv 32 := 0x00008067.
Lemma F_9644c : fetch_word AsanUbsan.M.loaded_segments (0x96494 : word) = Some W_9644c.
Proof. vm_refl. Qed.
Lemma D_9644c : decode_any W_9644c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967bc : bv 32 := 0x00060693.
Lemma F_967bc : fetch_word AsanUbsan.M.loaded_segments (0x96804 : word) = Some W_967bc.
Proof. vm_refl. Qed.
Lemma D_967bc : decode_any W_967bc = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967c0 : bv 32 := 0x00000613.
Lemma F_967c0 : fetch_word AsanUbsan.M.loaded_segments (0x96808 : word) = Some W_967c0.
Proof. vm_refl. Qed.
Lemma D_967c0 : decode_any W_967c0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967c4 : bv 32 := 0x0040006f.
Lemma F_967c4 : fetch_word AsanUbsan.M.loaded_segments (0x9680c : word) = Some W_967c4.
Proof. vm_refl. Qed.
Lemma D_967c4 : decode_any W_967c4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967c8 : bv 32 := 0xfa010113.
Lemma F_967c8 : fetch_word AsanUbsan.M.loaded_segments (0x96810 : word) = Some W_967c8.
Proof. vm_refl. Qed.
Lemma D_967c8 : decode_any W_967c8 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967cc : bv 32 := 0x04113c23.
Lemma F_967cc : fetch_word AsanUbsan.M.loaded_segments (0x96814 : word) = Some W_967cc.
Proof. vm_refl. Qed.
Lemma D_967cc : decode_any W_967cc = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967d0 : bv 32 := 0x04813823.
Lemma F_967d0 : fetch_word AsanUbsan.M.loaded_segments (0x96818 : word) = Some W_967d0.
Proof. vm_refl. Qed.
Lemma D_967d0 : decode_any W_967d0 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967d4 : bv 32 := 0x04913423.
Lemma F_967d4 : fetch_word AsanUbsan.M.loaded_segments (0x9681c : word) = Some W_967d4.
Proof. vm_refl. Qed.
Lemma D_967d4 : decode_any W_967d4 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967d8 : bv 32 := 0x05213023.
Lemma F_967d8 : fetch_word AsanUbsan.M.loaded_segments (0x96820 : word) = Some W_967d8.
Proof. vm_refl. Qed.
Lemma D_967d8 : decode_any W_967d8 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967dc : bv 32 := 0x03313c23.
Lemma F_967dc : fetch_word AsanUbsan.M.loaded_segments (0x96824 : word) = Some W_967dc.
Proof. vm_refl. Qed.
Lemma D_967dc : decode_any W_967dc = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967e0 : bv 32 := 0x03413823.
Lemma F_967e0 : fetch_word AsanUbsan.M.loaded_segments (0x96828 : word) = Some W_967e0.
Proof. vm_refl. Qed.
Lemma D_967e0 : decode_any W_967e0 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967e4 : bv 32 := 0x00068993.
Lemma F_967e4 : fetch_word AsanUbsan.M.loaded_segments (0x9682c : word) = Some W_967e4.
Proof. vm_refl. Qed.
Lemma D_967e4 : decode_any W_967e4 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967e8 : bv 32 := 0x00060493.
Lemma F_967e8 : fetch_word AsanUbsan.M.loaded_segments (0x96830 : word) = Some W_967e8.
Proof. vm_refl. Qed.
Lemma D_967e8 : decode_any W_967e8 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967ec : bv 32 := 0x00058413.
Lemma F_967ec : fetch_word AsanUbsan.M.loaded_segments (0x96834 : word) = Some W_967ec.
Proof. vm_refl. Qed.
Lemma D_967ec : decode_any W_967ec = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967f0 : bv 32 := 0x000ce597.
Lemma F_967f0 : fetch_word AsanUbsan.M.loaded_segments (0x96838 : word) = Some W_967f0.
Proof. vm_refl. Qed.
Lemma D_967f0 : decode_any W_967f0 = Some (Auipc 11 206, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967f4 : bv 32 := 0xcc05ba03.
Lemma F_967f4 : fetch_word AsanUbsan.M.loaded_segments (0x9683c : word) = Some W_967f4.
Proof. vm_refl. Qed.
Lemma D_967f4 : decode_any W_967f4 = Some (Load SZ8 true 20 11 3264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967f8 : bv 32 := 0x000a3583.
Lemma F_967f8 : fetch_word AsanUbsan.M.loaded_segments (0x96840 : word) = Some W_967f8.
Proof. vm_refl. Qed.
Lemma D_967f8 : decode_any W_967f8 = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967fc : bv 32 := 0x00050913.
Lemma F_967fc : fetch_word AsanUbsan.M.loaded_segments (0x96844 : word) = Some W_967fc.
Proof. vm_refl. Qed.
Lemma D_967fc : decode_any W_967fc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96800 : bv 32 := 0x00059863.
Lemma F_96800 : fetch_word AsanUbsan.M.loaded_segments (0x96848 : word) = Some W_96800.
Proof. vm_refl. Qed.
Lemma D_96800 : decode_any W_96800 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96810 : bv 32 := 0xfff58513.
Lemma F_96810 : fetch_word AsanUbsan.M.loaded_segments (0x96858 : word) = Some W_96810.
Proof. vm_refl. Qed.
Lemma D_96810 : decode_any W_96810 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96814 : bv 32 := 0x00a5f533.
Lemma F_96814 : fetch_word AsanUbsan.M.loaded_segments (0x9685c : word) = Some W_96814.
Proof. vm_refl. Qed.
Lemma D_96814 : decode_any W_96814 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96818 : bv 32 := 0x0a051863.
Lemma F_96818 : fetch_word AsanUbsan.M.loaded_segments (0x96860 : word) = Some W_96818.
Proof. vm_refl. Qed.
Lemma D_96818 : decode_any W_96818 = Some (Branch BC_NE 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9681c : bv 32 := 0x00b40433.
Lemma F_9681c : fetch_word AsanUbsan.M.loaded_segments (0x96864 : word) = Some W_9681c.
Proof. vm_refl. Qed.
Lemma D_9681c : decode_any W_9681c = Some (Op ALU_ADD 8 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96820 : bv 32 := 0xfff40413.
Lemma F_96820 : fetch_word AsanUbsan.M.loaded_segments (0x96868 : word) = Some W_96820.
Proof. vm_refl. Qed.
Lemma D_96820 : decode_any W_96820 = Some (OpImm ALU_ADD 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96824 : bv 32 := 0x40b00533.
Lemma F_96824 : fetch_word AsanUbsan.M.loaded_segments (0x9686c : word) = Some W_96824.
Proof. vm_refl. Qed.
Lemma D_96824 : decode_any W_96824 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96828 : bv 32 := 0x00a47433.
Lemma F_96828 : fetch_word AsanUbsan.M.loaded_segments (0x96870 : word) = Some W_96828.
Proof. vm_refl. Qed.
Lemma D_96828 : decode_any W_96828 = Some (Op ALU_AND 8 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9682c : bv 32 := 0x00059863.
Lemma F_9682c : fetch_word AsanUbsan.M.loaded_segments (0x96874 : word) = Some W_9682c.
Proof. vm_refl. Qed.
Lemma D_9682c : decode_any W_9682c = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9683c : bv 32 := 0x00a97933.
Lemma F_9683c : fetch_word AsanUbsan.M.loaded_segments (0x96884 : word) = Some W_9683c.
Proof. vm_refl. Qed.
Lemma D_9683c : decode_any W_9683c = Some (Op ALU_AND 18 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96840 : bv 32 := 0x03200513.
Lemma F_96840 : fetch_word AsanUbsan.M.loaded_segments (0x96888 : word) = Some W_96840.
Proof. vm_refl. Qed.
Lemma D_96840 : decode_any W_96840 = Some (OpImm ALU_ADD 10 0 50, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96844 : bv 32 := 0x00a12023.
Lemma F_96844 : fetch_word AsanUbsan.M.loaded_segments (0x9688c : word) = Some W_96844.
Proof. vm_refl. Qed.
Lemma D_96844 : decode_any W_96844 = Some (Store SZ4 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96848 : bv 32 := 0x00010613.
Lemma F_96848 : fetch_word AsanUbsan.M.loaded_segments (0x96890 : word) = Some W_96848.
Proof. vm_refl. Qed.
Lemma D_96848 : decode_any W_96848 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9684c : bv 32 := 0x00098513.
Lemma F_9684c : fetch_word AsanUbsan.M.loaded_segments (0x96894 : word) = Some W_9684c.
Proof. vm_refl. Qed.
Lemma D_9684c : decode_any W_9684c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96850 : bv 32 := 0x00040593.
Lemma F_96850 : fetch_word AsanUbsan.M.loaded_segments (0x96898 : word) = Some W_96850.
Proof. vm_refl. Qed.
Lemma D_96850 : decode_any W_96850 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96854 : bv 32 := 0x608000ef.
Lemma F_96854 : fetch_word AsanUbsan.M.loaded_segments (0x9689c : word) = Some W_96854.
Proof. vm_refl. Qed.
Lemma D_96854 : decode_any W_96854 = Some (Jal 1 1544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96858 : bv 32 := 0x00012683.
Lemma F_96858 : fetch_word AsanUbsan.M.loaded_segments (0x968a0 : word) = Some W_96858.
Proof. vm_refl. Qed.
Lemma D_96858 : decode_any W_96858 = Some (Load SZ4 true 13 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9685c : bv 32 := 0x00050713.
Lemma F_9685c : fetch_word AsanUbsan.M.loaded_segments (0x968a4 : word) = Some W_9685c.
Proof. vm_refl. Qed.
Lemma D_9685c : decode_any W_9685c = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96860 : bv 32 := 0x00300613.
Lemma F_96860 : fetch_word AsanUbsan.M.loaded_segments (0x968a8 : word) = Some W_96860.
Proof. vm_refl. Qed.
Lemma D_96860 : decode_any W_96860 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96864 : bv 32 := 0x00090513.
Lemma F_96864 : fetch_word AsanUbsan.M.loaded_segments (0x968ac : word) = Some W_96864.
Proof. vm_refl. Qed.
Lemma D_96864 : decode_any W_96864 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96868 : bv 32 := 0x00040593.
Lemma F_96868 : fetch_word AsanUbsan.M.loaded_segments (0x968b0 : word) = Some W_96868.
Proof. vm_refl. Qed.
Lemma D_96868 : decode_any W_96868 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9686c : bv 32 := 0x00000793.
Lemma F_9686c : fetch_word AsanUbsan.M.loaded_segments (0x968b4 : word) = Some W_9686c.
Proof. vm_refl. Qed.
Lemma D_9686c : decode_any W_9686c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96870 : bv 32 := 0xa40fe0ef.
Lemma F_96870 : fetch_word AsanUbsan.M.loaded_segments (0x968b8 : word) = Some W_96870.
Proof. vm_refl. Qed.
Lemma D_96870 : decode_any W_96870 = Some (Jal 1 2089536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96874 : bv 32 := 0x00050993.
Lemma F_96874 : fetch_word AsanUbsan.M.loaded_segments (0x968bc : word) = Some W_96874.
Proof. vm_refl. Qed.
Lemma D_96874 : decode_any W_96874 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96878 : bv 32 := 0x00000593.
Lemma F_96878 : fetch_word AsanUbsan.M.loaded_segments (0x968c0 : word) = Some W_96878.
Proof. vm_refl. Qed.
Lemma D_96878 : decode_any W_96878 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9687c : bv 32 := 0xa14fe0ef.
Lemma F_9687c : fetch_word AsanUbsan.M.loaded_segments (0x968c4 : word) = Some W_9687c.
Proof. vm_refl. Qed.
Lemma D_9687c : decode_any W_9687c = Some (Jal 1 2089492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96880 : bv 32 := 0xaaaab537.
Lemma F_96880 : fetch_word AsanUbsan.M.loaded_segments (0x968c8 : word) = Some W_96880.
Proof. vm_refl. Qed.
Lemma D_96880 : decode_any W_96880 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96884 : bv 32 := 0xaaa50513.
Lemma F_96884 : fetch_word AsanUbsan.M.loaded_segments (0x968cc : word) = Some W_96884.
Proof. vm_refl. Qed.
Lemma D_96884 : decode_any W_96884 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96888 : bv 32 := 0x02a12623.
Lemma F_96888 : fetch_word AsanUbsan.M.loaded_segments (0x968d0 : word) = Some W_96888.
Proof. vm_refl. Qed.
Lemma D_96888 : decode_any W_96888 = Some (Store SZ4 2 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9688c : bv 32 := 0x02c10593.
Lemma F_9688c : fetch_word AsanUbsan.M.loaded_segments (0x968d4 : word) = Some W_9688c.
Proof. vm_refl. Qed.
Lemma D_9688c : decode_any W_9688c = Some (OpImm ALU_ADD 11 2 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96890 : bv 32 := 0x00098513.
Lemma F_96890 : fetch_word AsanUbsan.M.loaded_segments (0x968d8 : word) = Some W_96890.
Proof. vm_refl. Qed.
Lemma D_96890 : decode_any W_96890 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96894 : bv 32 := 0x9fcfe0ef.
Lemma F_96894 : fetch_word AsanUbsan.M.loaded_segments (0x968dc : word) = Some W_96894.
Proof. vm_refl. Qed.
Lemma D_96894 : decode_any W_96894 = Some (Jal 1 2089468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96898 : bv 32 := 0x04051063.
Lemma F_96898 : fetch_word AsanUbsan.M.loaded_segments (0x968e0 : word) = Some W_96898.
Proof. vm_refl. Qed.
Lemma D_96898 : decode_any W_96898 = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9689c : bv 32 := 0x00040513.
Lemma F_9689c : fetch_word AsanUbsan.M.loaded_segments (0x968e4 : word) = Some W_9689c.
Proof. vm_refl. Qed.
Lemma D_9689c : decode_any W_9689c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968a0 : bv 32 := 0x8d8fa0ef.
Lemma F_968a0 : fetch_word AsanUbsan.M.loaded_segments (0x968e8 : word) = Some W_968a0.
Proof. vm_refl. Qed.
Lemma D_968a0 : decode_any W_968a0 = Some (Jal 1 2072792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968a4 : bv 32 := 0x00098513.
Lemma F_968a4 : fetch_word AsanUbsan.M.loaded_segments (0x968ec : word) = Some W_968a4.
Proof. vm_refl. Qed.
Lemma D_968a4 : decode_any W_968a4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968a8 : bv 32 := 0x05813083.
Lemma F_968a8 : fetch_word AsanUbsan.M.loaded_segments (0x968f0 : word) = Some W_968a8.
Proof. vm_refl. Qed.
Lemma D_968a8 : decode_any W_968a8 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968ac : bv 32 := 0x05013403.
Lemma F_968ac : fetch_word AsanUbsan.M.loaded_segments (0x968f4 : word) = Some W_968ac.
Proof. vm_refl. Qed.
Lemma D_968ac : decode_any W_968ac = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968b0 : bv 32 := 0x04813483.
Lemma F_968b0 : fetch_word AsanUbsan.M.loaded_segments (0x968f8 : word) = Some W_968b0.
Proof. vm_refl. Qed.
Lemma D_968b0 : decode_any W_968b0 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968b4 : bv 32 := 0x04013903.
Lemma F_968b4 : fetch_word AsanUbsan.M.loaded_segments (0x968fc : word) = Some W_968b4.
Proof. vm_refl. Qed.
Lemma D_968b4 : decode_any W_968b4 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968b8 : bv 32 := 0x03813983.
Lemma F_968b8 : fetch_word AsanUbsan.M.loaded_segments (0x96900 : word) = Some W_968b8.
Proof. vm_refl. Qed.
Lemma D_968b8 : decode_any W_968b8 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968bc : bv 32 := 0x03013a03.
Lemma F_968bc : fetch_word AsanUbsan.M.loaded_segments (0x96904 : word) = Some W_968bc.
Proof. vm_refl. Qed.
Lemma D_968bc : decode_any W_968bc = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968c0 : bv 32 := 0x06010113.
Lemma F_968c0 : fetch_word AsanUbsan.M.loaded_segments (0x96908 : word) = Some W_968c0.
Proof. vm_refl. Qed.
Lemma D_968c0 : decode_any W_968c0 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968c4 : bv 32 := 0x00008067.
Lemma F_968c4 : fetch_word AsanUbsan.M.loaded_segments (0x9690c : word) = Some W_968c4.
Proof. vm_refl. Qed.
Lemma D_968c4 : decode_any W_968c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96940 : bv 32 := 0x00060693.
Lemma F_96940 : fetch_word AsanUbsan.M.loaded_segments (0x96988 : word) = Some W_96940.
Proof. vm_refl. Qed.
Lemma D_96940 : decode_any W_96940 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96944 : bv 32 := 0x00100613.
Lemma F_96944 : fetch_word AsanUbsan.M.loaded_segments (0x9698c : word) = Some W_96944.
Proof. vm_refl. Qed.
Lemma D_96944 : decode_any W_96944 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96948 : bv 32 := 0xe81ff06f.
Lemma F_96948 : fetch_word AsanUbsan.M.loaded_segments (0x96990 : word) = Some W_96948.
Proof. vm_refl. Qed.
Lemma D_96948 : decode_any W_96948 = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e5c : bv 32 := 0xef010113.
Lemma F_96e5c : fetch_word AsanUbsan.M.loaded_segments (0x96ea4 : word) = Some W_96e5c.
Proof. vm_refl. Qed.
Lemma D_96e5c : decode_any W_96e5c = Some (OpImm ALU_ADD 2 2 3824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e60 : bv 32 := 0x10113423.
Lemma F_96e60 : fetch_word AsanUbsan.M.loaded_segments (0x96ea8 : word) = Some W_96e60.
Proof. vm_refl. Qed.
Lemma D_96e60 : decode_any W_96e60 = Some (Store SZ8 2 1 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e64 : bv 32 := 0x10813023.
Lemma F_96e64 : fetch_word AsanUbsan.M.loaded_segments (0x96eac : word) = Some W_96e64.
Proof. vm_refl. Qed.
Lemma D_96e64 : decode_any W_96e64 = Some (Store SZ8 2 8 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e68 : bv 32 := 0x0e913c23.
Lemma F_96e68 : fetch_word AsanUbsan.M.loaded_segments (0x96eb0 : word) = Some W_96e68.
Proof. vm_refl. Qed.
Lemma D_96e68 : decode_any W_96e68 = Some (Store SZ8 2 9 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e6c : bv 32 := 0x0f213823.
Lemma F_96e6c : fetch_word AsanUbsan.M.loaded_segments (0x96eb4 : word) = Some W_96e6c.
Proof. vm_refl. Qed.
Lemma D_96e6c : decode_any W_96e6c = Some (Store SZ8 2 18 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e70 : bv 32 := 0x0f313423.
Lemma F_96e70 : fetch_word AsanUbsan.M.loaded_segments (0x96eb8 : word) = Some W_96e70.
Proof. vm_refl. Qed.
Lemma D_96e70 : decode_any W_96e70 = Some (Store SZ8 2 19 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e74 : bv 32 := 0x0f413023.
Lemma F_96e74 : fetch_word AsanUbsan.M.loaded_segments (0x96ebc : word) = Some W_96e74.
Proof. vm_refl. Qed.
Lemma D_96e74 : decode_any W_96e74 = Some (Store SZ8 2 20 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e78 : bv 32 := 0x0d513c23.
Lemma F_96e78 : fetch_word AsanUbsan.M.loaded_segments (0x96ec0 : word) = Some W_96e78.
Proof. vm_refl. Qed.
Lemma D_96e78 : decode_any W_96e78 = Some (Store SZ8 2 21 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e7c : bv 32 := 0x00050913.
Lemma F_96e7c : fetch_word AsanUbsan.M.loaded_segments (0x96ec4 : word) = Some W_96e7c.
Proof. vm_refl. Qed.
Lemma D_96e7c : decode_any W_96e7c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e80 : bv 32 := 0xfff00513.
Lemma F_96e80 : fetch_word AsanUbsan.M.loaded_segments (0x96ec8 : word) = Some W_96e80.
Proof. vm_refl. Qed.
Lemma D_96e80 : decode_any W_96e80 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e84 : bv 32 := 0x12090463.
Lemma F_96e84 : fetch_word AsanUbsan.M.loaded_segments (0x96ecc : word) = Some W_96e84.
Proof. vm_refl. Qed.
Lemma D_96e84 : decode_any W_96e84 = Some (Branch BC_EQ 18 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e88 : bv 32 := 0x00060413.
Lemma F_96e88 : fetch_word AsanUbsan.M.loaded_segments (0x96ed0 : word) = Some W_96e88.
Proof. vm_refl. Qed.
Lemma D_96e88 : decode_any W_96e88 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e8c : bv 32 := 0x000cd617.
Lemma F_96e8c : fetch_word AsanUbsan.M.loaded_segments (0x96ed4 : word) = Some W_96e8c.
Proof. vm_refl. Qed.
Lemma D_96e8c : decode_any W_96e8c = Some (Auipc 12 205, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e90 : bv 32 := 0x63463603.
Lemma F_96e90 : fetch_word AsanUbsan.M.loaded_segments (0x96ed8 : word) = Some W_96e90.
Proof. vm_refl. Qed.
Lemma D_96e90 : decode_any W_96e90 = Some (Load SZ8 true 12 12 1588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e94 : bv 32 := 0x10464603.
Lemma F_96e94 : fetch_word AsanUbsan.M.loaded_segments (0x96edc : word) = Some W_96e94.
Proof. vm_refl. Qed.
Lemma D_96e94 : decode_any W_96e94 = Some (Load SZ1 false 12 12 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e98 : bv 32 := 0x00167613.
Lemma F_96e98 : fetch_word AsanUbsan.M.loaded_segments (0x96ee0 : word) = Some W_96e98.
Proof. vm_refl. Qed.
Lemma D_96e98 : decode_any W_96e98 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96e9c : bv 32 := 0x10060863.
Lemma F_96e9c : fetch_word AsanUbsan.M.loaded_segments (0x96ee4 : word) = Some W_96e9c.
Proof. vm_refl. Qed.
Lemma D_96e9c : decode_any W_96e9c = Some (Branch BC_EQ 12 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96fac : bv 32 := 0x0005051b.
Lemma F_96fac : fetch_word AsanUbsan.M.loaded_segments (0x96ff4 : word) = Some W_96fac.
Proof. vm_refl. Qed.
Lemma D_96fac : decode_any W_96fac = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96fb0 : bv 32 := 0x10813083.
Lemma F_96fb0 : fetch_word AsanUbsan.M.loaded_segments (0x96ff8 : word) = Some W_96fb0.
Proof. vm_refl. Qed.
Lemma D_96fb0 : decode_any W_96fb0 = Some (Load SZ8 true 1 2 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96fb4 : bv 32 := 0x10013403.
Lemma F_96fb4 : fetch_word AsanUbsan.M.loaded_segments (0x96ffc : word) = Some W_96fb4.
Proof. vm_refl. Qed.
Lemma D_96fb4 : decode_any W_96fb4 = Some (Load SZ8 true 8 2 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96fb8 : bv 32 := 0x0f813483.
Lemma F_96fb8 : fetch_word AsanUbsan.M.loaded_segments (0x97000 : word) = Some W_96fb8.
Proof. vm_refl. Qed.
Lemma D_96fb8 : decode_any W_96fb8 = Some (Load SZ8 true 9 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96fbc : bv 32 := 0x0f013903.
Lemma F_96fbc : fetch_word AsanUbsan.M.loaded_segments (0x97004 : word) = Some W_96fbc.
Proof. vm_refl. Qed.
Lemma D_96fbc : decode_any W_96fbc = Some (Load SZ8 true 18 2 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96fc0 : bv 32 := 0x0e813983.
Lemma F_96fc0 : fetch_word AsanUbsan.M.loaded_segments (0x97008 : word) = Some W_96fc0.
Proof. vm_refl. Qed.
Lemma D_96fc0 : decode_any W_96fc0 = Some (Load SZ8 true 19 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96fc4 : bv 32 := 0x0e013a03.
Lemma F_96fc4 : fetch_word AsanUbsan.M.loaded_segments (0x9700c : word) = Some W_96fc4.
Proof. vm_refl. Qed.
Lemma D_96fc4 : decode_any W_96fc4 = Some (Load SZ8 true 20 2 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96fc8 : bv 32 := 0x0d813a83.
Lemma F_96fc8 : fetch_word AsanUbsan.M.loaded_segments (0x97010 : word) = Some W_96fc8.
Proof. vm_refl. Qed.
Lemma D_96fc8 : decode_any W_96fc8 = Some (Load SZ8 true 21 2 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96fcc : bv 32 := 0x11010113.
Lemma F_96fcc : fetch_word AsanUbsan.M.loaded_segments (0x97014 : word) = Some W_96fcc.
Proof. vm_refl. Qed.
Lemma D_96fcc : decode_any W_96fcc = Some (OpImm ALU_ADD 2 2 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96fd0 : bv 32 := 0x00008067.
Lemma F_96fd0 : fetch_word AsanUbsan.M.loaded_segments (0x97018 : word) = Some W_96fd0.
Proof. vm_refl. Qed.
Lemma D_96fd0 : decode_any W_96fd0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

