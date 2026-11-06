(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushU9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_66940 : bv 32 := 0xfe010113.
Lemma F_66940 : fetch_word Ubsan.M.loaded_segments (0x66998 : word) = Some W_66940.
Proof. vm_refl. Qed.
Lemma D_66940 : decode_any W_66940 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66944 : bv 32 := 0x00113c23.
Lemma F_66944 : fetch_word Ubsan.M.loaded_segments (0x6699c : word) = Some W_66944.
Proof. vm_refl. Qed.
Lemma D_66944 : decode_any W_66944 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66948 : bv 32 := 0x00813823.
Lemma F_66948 : fetch_word Ubsan.M.loaded_segments (0x669a0 : word) = Some W_66948.
Proof. vm_refl. Qed.
Lemma D_66948 : decode_any W_66948 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6694c : bv 32 := 0x00913423.
Lemma F_6694c : fetch_word Ubsan.M.loaded_segments (0x669a4 : word) = Some W_6694c.
Proof. vm_refl. Qed.
Lemma D_6694c : decode_any W_6694c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66950 : bv 32 := 0x06050c63.
Lemma F_66950 : fetch_word Ubsan.M.loaded_segments (0x669a8 : word) = Some W_66950.
Proof. vm_refl. Qed.
Lemma D_66950 : decode_any W_66950 = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66954 : bv 32 := 0x00050413.
Lemma F_66954 : fetch_word Ubsan.M.loaded_segments (0x669ac : word) = Some W_66954.
Proof. vm_refl. Qed.
Lemma D_66954 : decode_any W_66954 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66958 : bv 32 := 0x00410613.
Lemma F_66958 : fetch_word Ubsan.M.loaded_segments (0x669b0 : word) = Some W_66958.
Proof. vm_refl. Qed.
Lemma D_66958 : decode_any W_66958 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6695c : bv 32 := 0x00000593.
Lemma F_6695c : fetch_word Ubsan.M.loaded_segments (0x669b4 : word) = Some W_6695c.
Proof. vm_refl. Qed.
Lemma D_6695c : decode_any W_6695c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66960 : bv 32 := 0x0f8000ef.
Lemma F_66960 : fetch_word Ubsan.M.loaded_segments (0x669b8 : word) = Some W_66960.
Proof. vm_refl. Qed.
Lemma D_66960 : decode_any W_66960 = Some (Jal 1 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66964 : bv 32 := 0x00412503.
Lemma F_66964 : fetch_word Ubsan.M.loaded_segments (0x669bc : word) = Some W_66964.
Proof. vm_refl. Qed.
Lemma D_66964 : decode_any W_66964 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66968 : bv 32 := 0x08050e63.
Lemma F_66968 : fetch_word Ubsan.M.loaded_segments (0x669c0 : word) = Some W_66968.
Proof. vm_refl. Qed.
Lemma D_66968 : decode_any W_66968 = Some (Branch BC_EQ 10 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6696c : bv 32 := 0x00100513.
Lemma F_6696c : fetch_word Ubsan.M.loaded_segments (0x669c4 : word) = Some W_6696c.
Proof. vm_refl. Qed.
Lemma D_6696c : decode_any W_6696c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66970 : bv 32 := 0x01800593.
Lemma F_66970 : fetch_word Ubsan.M.loaded_segments (0x669c8 : word) = Some W_66970.
Proof. vm_refl. Qed.
Lemma D_66970 : decode_any W_66970 = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66974 : bv 32 := 0x2b57b0ef.
Lemma F_66974 : fetch_word Ubsan.M.loaded_segments (0x669cc : word) = Some W_66974.
Proof. vm_refl. Qed.
Lemma D_66974 : decode_any W_66974 = Some (Jal 1 506548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66978 : bv 32 := 0x00747593.
Lemma F_66978 : fetch_word Ubsan.M.loaded_segments (0x669d0 : word) = Some W_66978.
Proof. vm_refl. Qed.
Lemma D_66978 : decode_any W_66978 = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6697c : bv 32 := 0x0c059c63.
Lemma F_6697c : fetch_word Ubsan.M.loaded_segments (0x669d4 : word) = Some W_6697c.
Proof. vm_refl. Qed.
Lemma D_6697c : decode_any W_6697c = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66980 : bv 32 := 0x00050493.
Lemma F_66980 : fetch_word Ubsan.M.loaded_segments (0x669d8 : word) = Some W_66980.
Proof. vm_refl. Qed.
Lemma D_66980 : decode_any W_66980 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66984 : bv 32 := 0x00c42503.
Lemma F_66984 : fetch_word Ubsan.M.loaded_segments (0x669dc : word) = Some W_66984.
Proof. vm_refl. Qed.
Lemma D_66984 : decode_any W_66984 = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66988 : bv 32 := 0x0025159b.
Lemma F_66988 : fetch_word Ubsan.M.loaded_segments (0x669e0 : word) = Some W_66988.
Proof. vm_refl. Qed.
Lemma D_66988 : decode_any W_66988 = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6698c : bv 32 := 0x00100513.
Lemma F_6698c : fetch_word Ubsan.M.loaded_segments (0x669e4 : word) = Some W_6698c.
Proof. vm_refl. Qed.
Lemma D_6698c : decode_any W_6698c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66990 : bv 32 := 0x2997b0ef.
Lemma F_66990 : fetch_word Ubsan.M.loaded_segments (0x669e8 : word) = Some W_66990.
Proof. vm_refl. Qed.
Lemma D_66990 : decode_any W_66990 = Some (Jal 1 506520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66994 : bv 32 := 0x0c048063.
Lemma F_66994 : fetch_word Ubsan.M.loaded_segments (0x669ec : word) = Some W_66994.
Proof. vm_refl. Qed.
Lemma D_66994 : decode_any W_66994 = Some (Branch BC_EQ 9 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66998 : bv 32 := 0x0074f593.
Lemma F_66998 : fetch_word Ubsan.M.loaded_segments (0x669f0 : word) = Some W_66998.
Proof. vm_refl. Qed.
Lemma D_66998 : decode_any W_66998 = Some (OpImm ALU_AND 11 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6699c : bv 32 := 0x0a059c63.
Lemma F_6699c : fetch_word Ubsan.M.loaded_segments (0x669f4 : word) = Some W_6699c.
Proof. vm_refl. Qed.
Lemma D_6699c : decode_any W_6699c = Some (Branch BC_NE 11 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669a0 : bv 32 := 0x00a4b023.
Lemma F_669a0 : fetch_word Ubsan.M.loaded_segments (0x669f8 : word) = Some W_669a0.
Proof. vm_refl. Qed.
Lemma D_669a0 : decode_any W_669a0 = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669a4 : bv 32 := 0x01042603.
Lemma F_669a4 : fetch_word Ubsan.M.loaded_segments (0x669fc : word) = Some W_669a4.
Proof. vm_refl. Qed.
Lemma D_669a4 : decode_any W_669a4 = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669a8 : bv 32 := 0x00043583.
Lemma F_669a8 : fetch_word Ubsan.M.loaded_segments (0x66a00 : word) = Some W_669a8.
Proof. vm_refl. Qed.
Lemma D_669a8 : decode_any W_669a8 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669ac : bv 32 := 0x00261613.
Lemma F_669ac : fetch_word Ubsan.M.loaded_segments (0x66a04 : word) = Some W_669ac.
Proof. vm_refl. Qed.
Lemma D_669ac : decode_any W_669ac = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669b0 : bv 32 := 0x0808a0ef.
Lemma F_669b0 : fetch_word Ubsan.M.loaded_segments (0x66a08 : word) = Some W_669b0.
Proof. vm_refl. Qed.
Lemma D_669b0 : decode_any W_669b0 = Some (Jal 1 565376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669b4 : bv 32 := 0x01042503.
Lemma F_669b4 : fetch_word Ubsan.M.loaded_segments (0x66a0c : word) = Some W_669b4.
Proof. vm_refl. Qed.
Lemma D_669b4 : decode_any W_669b4 = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669b8 : bv 32 := 0x00a4a823.
Lemma F_669b8 : fetch_word Ubsan.M.loaded_segments (0x66a10 : word) = Some W_669b8.
Proof. vm_refl. Qed.
Lemma D_669b8 : decode_any W_669b8 = Some (Store SZ4 9 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669bc : bv 32 := 0x00843503.
Lemma F_669bc : fetch_word Ubsan.M.loaded_segments (0x66a14 : word) = Some W_669bc.
Proof. vm_refl. Qed.
Lemma D_669bc : decode_any W_669bc = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669c0 : bv 32 := 0x00a4b423.
Lemma F_669c0 : fetch_word Ubsan.M.loaded_segments (0x66a18 : word) = Some W_669c0.
Proof. vm_refl. Qed.
Lemma D_669c0 : decode_any W_669c0 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669c4 : bv 32 := 0x0780006f.
Lemma F_669c4 : fetch_word Ubsan.M.loaded_segments (0x66a1c : word) = Some W_669c4.
Proof. vm_refl. Qed.
Lemma D_669c4 : decode_any W_669c4 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a3c : bv 32 := 0x00048513.
Lemma F_66a3c : fetch_word Ubsan.M.loaded_segments (0x66a94 : word) = Some W_66a3c.
Proof. vm_refl. Qed.
Lemma D_66a3c : decode_any W_66a3c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a40 : bv 32 := 0x01813083.
Lemma F_66a40 : fetch_word Ubsan.M.loaded_segments (0x66a98 : word) = Some W_66a40.
Proof. vm_refl. Qed.
Lemma D_66a40 : decode_any W_66a40 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a44 : bv 32 := 0x01013403.
Lemma F_66a44 : fetch_word Ubsan.M.loaded_segments (0x66a9c : word) = Some W_66a44.
Proof. vm_refl. Qed.
Lemma D_66a44 : decode_any W_66a44 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a48 : bv 32 := 0x00813483.
Lemma F_66a48 : fetch_word Ubsan.M.loaded_segments (0x66aa0 : word) = Some W_66a48.
Proof. vm_refl. Qed.
Lemma D_66a48 : decode_any W_66a48 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a4c : bv 32 := 0x02010113.
Lemma F_66a4c : fetch_word Ubsan.M.loaded_segments (0x66aa4 : word) = Some W_66a4c.
Proof. vm_refl. Qed.
Lemma D_66a4c : decode_any W_66a4c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a50 : bv 32 := 0x00008067.
Lemma F_66a50 : fetch_word Ubsan.M.loaded_segments (0x66aa8 : word) = Some W_66a50.
Proof. vm_refl. Qed.
Lemma D_66a50 : decode_any W_66a50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

