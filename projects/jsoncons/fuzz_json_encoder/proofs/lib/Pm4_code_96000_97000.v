(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_96068 : bv 32 := 0x00060693.
Lemma F_96068 : fetch_word Asan.M.loaded_segments (0x960b8 : word) = Some W_96068.
Proof. vm_refl. Qed.
Lemma D_96068 : decode_any W_96068 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9606c : bv 32 := 0x00100613.
Lemma F_9606c : fetch_word Asan.M.loaded_segments (0x960bc : word) = Some W_9606c.
Proof. vm_refl. Qed.
Lemma D_9606c : decode_any W_9606c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96070 : bv 32 := 0xe81ff06f.
Lemma F_96070 : fetch_word Asan.M.loaded_segments (0x960c0 : word) = Some W_96070.
Proof. vm_refl. Qed.
Lemma D_96070 : decode_any W_96070 = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96584 : bv 32 := 0xef010113.
Lemma F_96584 : fetch_word Asan.M.loaded_segments (0x965d4 : word) = Some W_96584.
Proof. vm_refl. Qed.
Lemma D_96584 : decode_any W_96584 = Some (OpImm ALU_ADD 2 2 3824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96588 : bv 32 := 0x10113423.
Lemma F_96588 : fetch_word Asan.M.loaded_segments (0x965d8 : word) = Some W_96588.
Proof. vm_refl. Qed.
Lemma D_96588 : decode_any W_96588 = Some (Store SZ8 2 1 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9658c : bv 32 := 0x10813023.
Lemma F_9658c : fetch_word Asan.M.loaded_segments (0x965dc : word) = Some W_9658c.
Proof. vm_refl. Qed.
Lemma D_9658c : decode_any W_9658c = Some (Store SZ8 2 8 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96590 : bv 32 := 0x0e913c23.
Lemma F_96590 : fetch_word Asan.M.loaded_segments (0x965e0 : word) = Some W_96590.
Proof. vm_refl. Qed.
Lemma D_96590 : decode_any W_96590 = Some (Store SZ8 2 9 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96594 : bv 32 := 0x0f213823.
Lemma F_96594 : fetch_word Asan.M.loaded_segments (0x965e4 : word) = Some W_96594.
Proof. vm_refl. Qed.
Lemma D_96594 : decode_any W_96594 = Some (Store SZ8 2 18 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96598 : bv 32 := 0x0f313423.
Lemma F_96598 : fetch_word Asan.M.loaded_segments (0x965e8 : word) = Some W_96598.
Proof. vm_refl. Qed.
Lemma D_96598 : decode_any W_96598 = Some (Store SZ8 2 19 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9659c : bv 32 := 0x0f413023.
Lemma F_9659c : fetch_word Asan.M.loaded_segments (0x965ec : word) = Some W_9659c.
Proof. vm_refl. Qed.
Lemma D_9659c : decode_any W_9659c = Some (Store SZ8 2 20 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965a0 : bv 32 := 0x0d513c23.
Lemma F_965a0 : fetch_word Asan.M.loaded_segments (0x965f0 : word) = Some W_965a0.
Proof. vm_refl. Qed.
Lemma D_965a0 : decode_any W_965a0 = Some (Store SZ8 2 21 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965a4 : bv 32 := 0x00050913.
Lemma F_965a4 : fetch_word Asan.M.loaded_segments (0x965f4 : word) = Some W_965a4.
Proof. vm_refl. Qed.
Lemma D_965a4 : decode_any W_965a4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965a8 : bv 32 := 0xfff00513.
Lemma F_965a8 : fetch_word Asan.M.loaded_segments (0x965f8 : word) = Some W_965a8.
Proof. vm_refl. Qed.
Lemma D_965a8 : decode_any W_965a8 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965ac : bv 32 := 0x12090463.
Lemma F_965ac : fetch_word Asan.M.loaded_segments (0x965fc : word) = Some W_965ac.
Proof. vm_refl. Qed.
Lemma D_965ac : decode_any W_965ac = Some (Branch BC_EQ 18 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965b0 : bv 32 := 0x00060413.
Lemma F_965b0 : fetch_word Asan.M.loaded_segments (0x96600 : word) = Some W_965b0.
Proof. vm_refl. Qed.
Lemma D_965b0 : decode_any W_965b0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965b4 : bv 32 := 0x000ca617.
Lemma F_965b4 : fetch_word Asan.M.loaded_segments (0x96604 : word) = Some W_965b4.
Proof. vm_refl. Qed.
Lemma D_965b4 : decode_any W_965b4 = Some (Auipc 12 202, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965b8 : bv 32 := 0x60463603.
Lemma F_965b8 : fetch_word Asan.M.loaded_segments (0x96608 : word) = Some W_965b8.
Proof. vm_refl. Qed.
Lemma D_965b8 : decode_any W_965b8 = Some (Load SZ8 true 12 12 1540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965bc : bv 32 := 0x10464603.
Lemma F_965bc : fetch_word Asan.M.loaded_segments (0x9660c : word) = Some W_965bc.
Proof. vm_refl. Qed.
Lemma D_965bc : decode_any W_965bc = Some (Load SZ1 false 12 12 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965c0 : bv 32 := 0x00167613.
Lemma F_965c0 : fetch_word Asan.M.loaded_segments (0x96610 : word) = Some W_965c0.
Proof. vm_refl. Qed.
Lemma D_965c0 : decode_any W_965c0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965c4 : bv 32 := 0x10060863.
Lemma F_965c4 : fetch_word Asan.M.loaded_segments (0x96614 : word) = Some W_965c4.
Proof. vm_refl. Qed.
Lemma D_965c4 : decode_any W_965c4 = Some (Branch BC_EQ 12 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_966d4 : bv 32 := 0x0005051b.
Lemma F_966d4 : fetch_word Asan.M.loaded_segments (0x96724 : word) = Some W_966d4.
Proof. vm_refl. Qed.
Lemma D_966d4 : decode_any W_966d4 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_966d8 : bv 32 := 0x10813083.
Lemma F_966d8 : fetch_word Asan.M.loaded_segments (0x96728 : word) = Some W_966d8.
Proof. vm_refl. Qed.
Lemma D_966d8 : decode_any W_966d8 = Some (Load SZ8 true 1 2 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_966dc : bv 32 := 0x10013403.
Lemma F_966dc : fetch_word Asan.M.loaded_segments (0x9672c : word) = Some W_966dc.
Proof. vm_refl. Qed.
Lemma D_966dc : decode_any W_966dc = Some (Load SZ8 true 8 2 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_966e0 : bv 32 := 0x0f813483.
Lemma F_966e0 : fetch_word Asan.M.loaded_segments (0x96730 : word) = Some W_966e0.
Proof. vm_refl. Qed.
Lemma D_966e0 : decode_any W_966e0 = Some (Load SZ8 true 9 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_966e4 : bv 32 := 0x0f013903.
Lemma F_966e4 : fetch_word Asan.M.loaded_segments (0x96734 : word) = Some W_966e4.
Proof. vm_refl. Qed.
Lemma D_966e4 : decode_any W_966e4 = Some (Load SZ8 true 18 2 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_966e8 : bv 32 := 0x0e813983.
Lemma F_966e8 : fetch_word Asan.M.loaded_segments (0x96738 : word) = Some W_966e8.
Proof. vm_refl. Qed.
Lemma D_966e8 : decode_any W_966e8 = Some (Load SZ8 true 19 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_966ec : bv 32 := 0x0e013a03.
Lemma F_966ec : fetch_word Asan.M.loaded_segments (0x9673c : word) = Some W_966ec.
Proof. vm_refl. Qed.
Lemma D_966ec : decode_any W_966ec = Some (Load SZ8 true 20 2 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_966f0 : bv 32 := 0x0d813a83.
Lemma F_966f0 : fetch_word Asan.M.loaded_segments (0x96740 : word) = Some W_966f0.
Proof. vm_refl. Qed.
Lemma D_966f0 : decode_any W_966f0 = Some (Load SZ8 true 21 2 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_966f4 : bv 32 := 0x11010113.
Lemma F_966f4 : fetch_word Asan.M.loaded_segments (0x96744 : word) = Some W_966f4.
Proof. vm_refl. Qed.
Lemma D_966f4 : decode_any W_966f4 = Some (OpImm ALU_ADD 2 2 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_966f8 : bv 32 := 0x00008067.
Lemma F_966f8 : fetch_word Asan.M.loaded_segments (0x96748 : word) = Some W_966f8.
Proof. vm_refl. Qed.
Lemma D_966f8 : decode_any W_966f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

