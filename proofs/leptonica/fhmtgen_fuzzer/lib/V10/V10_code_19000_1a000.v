(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.H Require GcFlushU10.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_1931c : bv 32 := 0xfe010113.
Lemma F_1931c : fetch_word Ubsan.M.loaded_segments (0x19418 : word) = Some W_1931c.
Proof. vm_refl. Qed.
Lemma D_1931c : decode_any W_1931c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19320 : bv 32 := 0x00113c23.
Lemma F_19320 : fetch_word Ubsan.M.loaded_segments (0x1941c : word) = Some W_19320.
Proof. vm_refl. Qed.
Lemma D_19320 : decode_any W_19320 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19324 : bv 32 := 0x00813823.
Lemma F_19324 : fetch_word Ubsan.M.loaded_segments (0x19420 : word) = Some W_19324.
Proof. vm_refl. Qed.
Lemma D_19324 : decode_any W_19324 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19328 : bv 32 := 0x00913423.
Lemma F_19328 : fetch_word Ubsan.M.loaded_segments (0x19424 : word) = Some W_19328.
Proof. vm_refl. Qed.
Lemma D_19328 : decode_any W_19328 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1932c : bv 32 := 0x06050c63.
Lemma F_1932c : fetch_word Ubsan.M.loaded_segments (0x19428 : word) = Some W_1932c.
Proof. vm_refl. Qed.
Lemma D_1932c : decode_any W_1932c = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19330 : bv 32 := 0x00050413.
Lemma F_19330 : fetch_word Ubsan.M.loaded_segments (0x1942c : word) = Some W_19330.
Proof. vm_refl. Qed.
Lemma D_19330 : decode_any W_19330 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19334 : bv 32 := 0x00410613.
Lemma F_19334 : fetch_word Ubsan.M.loaded_segments (0x19430 : word) = Some W_19334.
Proof. vm_refl. Qed.
Lemma D_19334 : decode_any W_19334 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19338 : bv 32 := 0x00000593.
Lemma F_19338 : fetch_word Ubsan.M.loaded_segments (0x19434 : word) = Some W_19338.
Proof. vm_refl. Qed.
Lemma D_19338 : decode_any W_19338 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1933c : bv 32 := 0x0f8000ef.
Lemma F_1933c : fetch_word Ubsan.M.loaded_segments (0x19438 : word) = Some W_1933c.
Proof. vm_refl. Qed.
Lemma D_1933c : decode_any W_1933c = Some (Jal 1 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19340 : bv 32 := 0x00412503.
Lemma F_19340 : fetch_word Ubsan.M.loaded_segments (0x1943c : word) = Some W_19340.
Proof. vm_refl. Qed.
Lemma D_19340 : decode_any W_19340 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19344 : bv 32 := 0x08050e63.
Lemma F_19344 : fetch_word Ubsan.M.loaded_segments (0x19440 : word) = Some W_19344.
Proof. vm_refl. Qed.
Lemma D_19344 : decode_any W_19344 = Some (Branch BC_EQ 10 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19348 : bv 32 := 0x00100513.
Lemma F_19348 : fetch_word Ubsan.M.loaded_segments (0x19444 : word) = Some W_19348.
Proof. vm_refl. Qed.
Lemma D_19348 : decode_any W_19348 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1934c : bv 32 := 0x01800593.
Lemma F_1934c : fetch_word Ubsan.M.loaded_segments (0x19448 : word) = Some W_1934c.
Proof. vm_refl. Qed.
Lemma D_1934c : decode_any W_1934c = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19350 : bv 32 := 0x485110ef.
Lemma F_19350 : fetch_word Ubsan.M.loaded_segments (0x1944c : word) = Some W_19350.
Proof. vm_refl. Qed.
Lemma D_19350 : decode_any W_19350 = Some (Jal 1 72836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19354 : bv 32 := 0x00747593.
Lemma F_19354 : fetch_word Ubsan.M.loaded_segments (0x19450 : word) = Some W_19354.
Proof. vm_refl. Qed.
Lemma D_19354 : decode_any W_19354 = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19358 : bv 32 := 0x0c059c63.
Lemma F_19358 : fetch_word Ubsan.M.loaded_segments (0x19454 : word) = Some W_19358.
Proof. vm_refl. Qed.
Lemma D_19358 : decode_any W_19358 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1935c : bv 32 := 0x00050493.
Lemma F_1935c : fetch_word Ubsan.M.loaded_segments (0x19458 : word) = Some W_1935c.
Proof. vm_refl. Qed.
Lemma D_1935c : decode_any W_1935c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19360 : bv 32 := 0x00c42503.
Lemma F_19360 : fetch_word Ubsan.M.loaded_segments (0x1945c : word) = Some W_19360.
Proof. vm_refl. Qed.
Lemma D_19360 : decode_any W_19360 = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19364 : bv 32 := 0x0025159b.
Lemma F_19364 : fetch_word Ubsan.M.loaded_segments (0x19460 : word) = Some W_19364.
Proof. vm_refl. Qed.
Lemma D_19364 : decode_any W_19364 = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19368 : bv 32 := 0x00100513.
Lemma F_19368 : fetch_word Ubsan.M.loaded_segments (0x19464 : word) = Some W_19368.
Proof. vm_refl. Qed.
Lemma D_19368 : decode_any W_19368 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1936c : bv 32 := 0x469110ef.
Lemma F_1936c : fetch_word Ubsan.M.loaded_segments (0x19468 : word) = Some W_1936c.
Proof. vm_refl. Qed.
Lemma D_1936c : decode_any W_1936c = Some (Jal 1 72808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19370 : bv 32 := 0x0c048063.
Lemma F_19370 : fetch_word Ubsan.M.loaded_segments (0x1946c : word) = Some W_19370.
Proof. vm_refl. Qed.
Lemma D_19370 : decode_any W_19370 = Some (Branch BC_EQ 9 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19374 : bv 32 := 0x0074f593.
Lemma F_19374 : fetch_word Ubsan.M.loaded_segments (0x19470 : word) = Some W_19374.
Proof. vm_refl. Qed.
Lemma D_19374 : decode_any W_19374 = Some (OpImm ALU_AND 11 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19378 : bv 32 := 0x0a059c63.
Lemma F_19378 : fetch_word Ubsan.M.loaded_segments (0x19474 : word) = Some W_19378.
Proof. vm_refl. Qed.
Lemma D_19378 : decode_any W_19378 = Some (Branch BC_NE 11 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1937c : bv 32 := 0x00a4b023.
Lemma F_1937c : fetch_word Ubsan.M.loaded_segments (0x19478 : word) = Some W_1937c.
Proof. vm_refl. Qed.
Lemma D_1937c : decode_any W_1937c = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19380 : bv 32 := 0x01042603.
Lemma F_19380 : fetch_word Ubsan.M.loaded_segments (0x1947c : word) = Some W_19380.
Proof. vm_refl. Qed.
Lemma D_19380 : decode_any W_19380 = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19384 : bv 32 := 0x00043583.
Lemma F_19384 : fetch_word Ubsan.M.loaded_segments (0x19480 : word) = Some W_19384.
Proof. vm_refl. Qed.
Lemma D_19384 : decode_any W_19384 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19388 : bv 32 := 0x00261613.
Lemma F_19388 : fetch_word Ubsan.M.loaded_segments (0x19484 : word) = Some W_19388.
Proof. vm_refl. Qed.
Lemma D_19388 : decode_any W_19388 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1938c : bv 32 := 0x6b5180ef.
Lemma F_1938c : fetch_word Ubsan.M.loaded_segments (0x19488 : word) = Some W_1938c.
Proof. vm_refl. Qed.
Lemma D_1938c : decode_any W_1938c = Some (Jal 1 102068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19390 : bv 32 := 0x01042503.
Lemma F_19390 : fetch_word Ubsan.M.loaded_segments (0x1948c : word) = Some W_19390.
Proof. vm_refl. Qed.
Lemma D_19390 : decode_any W_19390 = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19394 : bv 32 := 0x00a4a823.
Lemma F_19394 : fetch_word Ubsan.M.loaded_segments (0x19490 : word) = Some W_19394.
Proof. vm_refl. Qed.
Lemma D_19394 : decode_any W_19394 = Some (Store SZ4 9 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19398 : bv 32 := 0x00843503.
Lemma F_19398 : fetch_word Ubsan.M.loaded_segments (0x19494 : word) = Some W_19398.
Proof. vm_refl. Qed.
Lemma D_19398 : decode_any W_19398 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1939c : bv 32 := 0x00a4b423.
Lemma F_1939c : fetch_word Ubsan.M.loaded_segments (0x19498 : word) = Some W_1939c.
Proof. vm_refl. Qed.
Lemma D_1939c : decode_any W_1939c = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193a0 : bv 32 := 0x0780006f.
Lemma F_193a0 : fetch_word Ubsan.M.loaded_segments (0x1949c : word) = Some W_193a0.
Proof. vm_refl. Qed.
Lemma D_193a0 : decode_any W_193a0 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19418 : bv 32 := 0x00048513.
Lemma F_19418 : fetch_word Ubsan.M.loaded_segments (0x19514 : word) = Some W_19418.
Proof. vm_refl. Qed.
Lemma D_19418 : decode_any W_19418 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1941c : bv 32 := 0x01813083.
Lemma F_1941c : fetch_word Ubsan.M.loaded_segments (0x19518 : word) = Some W_1941c.
Proof. vm_refl. Qed.
Lemma D_1941c : decode_any W_1941c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19420 : bv 32 := 0x01013403.
Lemma F_19420 : fetch_word Ubsan.M.loaded_segments (0x1951c : word) = Some W_19420.
Proof. vm_refl. Qed.
Lemma D_19420 : decode_any W_19420 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19424 : bv 32 := 0x00813483.
Lemma F_19424 : fetch_word Ubsan.M.loaded_segments (0x19520 : word) = Some W_19424.
Proof. vm_refl. Qed.
Lemma D_19424 : decode_any W_19424 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19428 : bv 32 := 0x02010113.
Lemma F_19428 : fetch_word Ubsan.M.loaded_segments (0x19524 : word) = Some W_19428.
Proof. vm_refl. Qed.
Lemma D_19428 : decode_any W_19428 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1942c : bv 32 := 0x00008067.
Lemma F_1942c : fetch_word Ubsan.M.loaded_segments (0x19528 : word) = Some W_1942c.
Proof. vm_refl. Qed.
Lemma D_1942c : decode_any W_1942c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
