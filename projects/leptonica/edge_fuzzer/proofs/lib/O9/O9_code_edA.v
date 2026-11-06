(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushS9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5dbcc : bv 32 := 0xfd010113.
Lemma F_5dbcc : fetch_word Plain.M.loaded_segments (0x5dc24 : word) = Some W_5dbcc.
Proof. vm_refl. Qed.
Lemma D_5dbcc : decode_any W_5dbcc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbd0 : bv 32 := 0x02113423.
Lemma F_5dbd0 : fetch_word Plain.M.loaded_segments (0x5dc28 : word) = Some W_5dbd0.
Proof. vm_refl. Qed.
Lemma D_5dbd0 : decode_any W_5dbd0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbd4 : bv 32 := 0x02813023.
Lemma F_5dbd4 : fetch_word Plain.M.loaded_segments (0x5dc2c : word) = Some W_5dbd4.
Proof. vm_refl. Qed.
Lemma D_5dbd4 : decode_any W_5dbd4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbd8 : bv 32 := 0x00913c23.
Lemma F_5dbd8 : fetch_word Plain.M.loaded_segments (0x5dc30 : word) = Some W_5dbd8.
Proof. vm_refl. Qed.
Lemma D_5dbd8 : decode_any W_5dbd8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbdc : bv 32 := 0x01213823.
Lemma F_5dbdc : fetch_word Plain.M.loaded_segments (0x5dc34 : word) = Some W_5dbdc.
Proof. vm_refl. Qed.
Lemma D_5dbdc : decode_any W_5dbdc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbe0 : bv 32 := 0x01313423.
Lemma F_5dbe0 : fetch_word Plain.M.loaded_segments (0x5dc38 : word) = Some W_5dbe0.
Proof. vm_refl. Qed.
Lemma D_5dbe0 : decode_any W_5dbe0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbe4 : bv 32 := 0x04050a63.
Lemma F_5dbe4 : fetch_word Plain.M.loaded_segments (0x5dc3c : word) = Some W_5dbe4.
Proof. vm_refl. Qed.
Lemma D_5dbe4 : decode_any W_5dbe4 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbe8 : bv 32 := 0x00050413.
Lemma F_5dbe8 : fetch_word Plain.M.loaded_segments (0x5dc40 : word) = Some W_5dbe8.
Proof. vm_refl. Qed.
Lemma D_5dbe8 : decode_any W_5dbe8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbec : bv 32 := 0x00053483.
Lemma F_5dbec : fetch_word Plain.M.loaded_segments (0x5dc44 : word) = Some W_5dbec.
Proof. vm_refl. Qed.
Lemma D_5dbec : decode_any W_5dbec = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbf0 : bv 32 := 0x08060663.
Lemma F_5dbf0 : fetch_word Plain.M.loaded_segments (0x5dc48 : word) = Some W_5dbf0.
Proof. vm_refl. Qed.
Lemma D_5dbf0 : decode_any W_5dbf0 = Some (Branch BC_EQ 12 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbf4 : bv 32 := 0x00058913.
Lemma F_5dbf4 : fetch_word Plain.M.loaded_segments (0x5dc4c : word) = Some W_5dbf4.
Proof. vm_refl. Qed.
Lemma D_5dbf4 : decode_any W_5dbf4 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbf8 : bv 32 := 0x00100513.
Lemma F_5dbf8 : fetch_word Plain.M.loaded_segments (0x5dc50 : word) = Some W_5dbf8.
Proof. vm_refl. Qed.
Lemma D_5dbf8 : decode_any W_5dbf8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dbfc : bv 32 := 0x00060993.
Lemma F_5dbfc : fetch_word Plain.M.loaded_segments (0x5dc54 : word) = Some W_5dbfc.
Proof. vm_refl. Qed.
Lemma D_5dbfc : decode_any W_5dbfc = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc00 : bv 32 := 0x00060593.
Lemma F_5dc00 : fetch_word Plain.M.loaded_segments (0x5dc58 : word) = Some W_5dc00.
Proof. vm_refl. Qed.
Lemma D_5dc00 : decode_any W_5dc00 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc04 : bv 32 := 0x471790ef.
Lemma F_5dc04 : fetch_word Plain.M.loaded_segments (0x5dc5c : word) = Some W_5dc04.
Proof. vm_refl. Qed.
Lemma D_5dc04 : decode_any W_5dc04 = Some (Jal 1 498800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc08 : bv 32 := 0x08048663.
Lemma F_5dc08 : fetch_word Plain.M.loaded_segments (0x5dc60 : word) = Some W_5dc08.
Proof. vm_refl. Qed.
Lemma D_5dc08 : decode_any W_5dc08 = Some (Branch BC_EQ 9 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc0c : bv 32 := 0x0a050a63.
Lemma F_5dc0c : fetch_word Plain.M.loaded_segments (0x5dc64 : word) = Some W_5dc0c.
Proof. vm_refl. Qed.
Lemma D_5dc0c : decode_any W_5dc0c = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc10 : bv 32 := 0x01396463.
Lemma F_5dc10 : fetch_word Plain.M.loaded_segments (0x5dc68 : word) = Some W_5dc10.
Proof. vm_refl. Qed.
Lemma D_5dc10 : decode_any W_5dc10 = Some (Branch BC_LTU 18 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc18 : bv 32 := 0x00050993.
Lemma F_5dc18 : fetch_word Plain.M.loaded_segments (0x5dc70 : word) = Some W_5dc18.
Proof. vm_refl. Qed.
Lemma D_5dc18 : decode_any W_5dc18 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc1c : bv 32 := 0x00048593.
Lemma F_5dc1c : fetch_word Plain.M.loaded_segments (0x5dc74 : word) = Some W_5dc1c.
Proof. vm_refl. Qed.
Lemma D_5dc1c : decode_any W_5dc1c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc20 : bv 32 := 0x00090613.
Lemma F_5dc20 : fetch_word Plain.M.loaded_segments (0x5dc78 : word) = Some W_5dc20.
Proof. vm_refl. Qed.
Lemma D_5dc20 : decode_any W_5dc20 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc24 : bv 32 := 0x258880ef.
Lemma F_5dc24 : fetch_word Plain.M.loaded_segments (0x5dc7c : word) = Some W_5dc24.
Proof. vm_refl. Qed.
Lemma D_5dc24 : decode_any W_5dc24 = Some (Jal 1 557656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc28 : bv 32 := 0x00048513.
Lemma F_5dc28 : fetch_word Plain.M.loaded_segments (0x5dc80 : word) = Some W_5dc28.
Proof. vm_refl. Qed.
Lemma D_5dc28 : decode_any W_5dc28 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc2c : bv 32 := 0x581790ef.
Lemma F_5dc2c : fetch_word Plain.M.loaded_segments (0x5dc84 : word) = Some W_5dc2c.
Proof. vm_refl. Qed.
Lemma D_5dc2c : decode_any W_5dc2c = Some (Jal 1 499072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc30 : bv 32 := 0x00098513.
Lemma F_5dc30 : fetch_word Plain.M.loaded_segments (0x5dc88 : word) = Some W_5dc30.
Proof. vm_refl. Qed.
Lemma D_5dc30 : decode_any W_5dc30 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc34 : bv 32 := 0x0580006f.
Lemma F_5dc34 : fetch_word Plain.M.loaded_segments (0x5dc8c : word) = Some W_5dc34.
Proof. vm_refl. Qed.
Lemma D_5dc34 : decode_any W_5dc34 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc8c : bv 32 := 0x00043023.
Lemma F_5dc8c : fetch_word Plain.M.loaded_segments (0x5dce4 : word) = Some W_5dc8c.
Proof. vm_refl. Qed.
Lemma D_5dc8c : decode_any W_5dc8c = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dc90 : bv 32 := 0x05c0006f.
Lemma F_5dc90 : fetch_word Plain.M.loaded_segments (0x5dce8 : word) = Some W_5dc90.
Proof. vm_refl. Qed.
Lemma D_5dc90 : decode_any W_5dc90 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcec : bv 32 := 0x02813083.
Lemma F_5dcec : fetch_word Plain.M.loaded_segments (0x5dd44 : word) = Some W_5dcec.
Proof. vm_refl. Qed.
Lemma D_5dcec : decode_any W_5dcec = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcf0 : bv 32 := 0x02013403.
Lemma F_5dcf0 : fetch_word Plain.M.loaded_segments (0x5dd48 : word) = Some W_5dcf0.
Proof. vm_refl. Qed.
Lemma D_5dcf0 : decode_any W_5dcf0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcf4 : bv 32 := 0x01813483.
Lemma F_5dcf4 : fetch_word Plain.M.loaded_segments (0x5dd4c : word) = Some W_5dcf4.
Proof. vm_refl. Qed.
Lemma D_5dcf4 : decode_any W_5dcf4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcf8 : bv 32 := 0x01013903.
Lemma F_5dcf8 : fetch_word Plain.M.loaded_segments (0x5dd50 : word) = Some W_5dcf8.
Proof. vm_refl. Qed.
Lemma D_5dcf8 : decode_any W_5dcf8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dcfc : bv 32 := 0x00813983.
Lemma F_5dcfc : fetch_word Plain.M.loaded_segments (0x5dd54 : word) = Some W_5dcfc.
Proof. vm_refl. Qed.
Lemma D_5dcfc : decode_any W_5dcfc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd00 : bv 32 := 0x03010113.
Lemma F_5dd00 : fetch_word Plain.M.loaded_segments (0x5dd58 : word) = Some W_5dd00.
Proof. vm_refl. Qed.
Lemma D_5dd00 : decode_any W_5dd00 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dd04 : bv 32 := 0x00008067.
Lemma F_5dd04 : fetch_word Plain.M.loaded_segments (0x5dd5c : word) = Some W_5dd04.
Proof. vm_refl. Qed.
Lemma D_5dd04 : decode_any W_5dd04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60994 : bv 32 := 0xfe010113.
Lemma F_60994 : fetch_word Plain.M.loaded_segments (0x609ec : word) = Some W_60994.
Proof. vm_refl. Qed.
Lemma D_60994 : decode_any W_60994 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60998 : bv 32 := 0x00113c23.
Lemma F_60998 : fetch_word Plain.M.loaded_segments (0x609f0 : word) = Some W_60998.
Proof. vm_refl. Qed.
Lemma D_60998 : decode_any W_60998 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6099c : bv 32 := 0x00813823.
Lemma F_6099c : fetch_word Plain.M.loaded_segments (0x609f4 : word) = Some W_6099c.
Proof. vm_refl. Qed.
Lemma D_6099c : decode_any W_6099c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609a0 : bv 32 := 0x00913423.
Lemma F_609a0 : fetch_word Plain.M.loaded_segments (0x609f8 : word) = Some W_609a0.
Proof. vm_refl. Qed.
Lemma D_609a0 : decode_any W_609a0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609a4 : bv 32 := 0x01213023.
Lemma F_609a4 : fetch_word Plain.M.loaded_segments (0x609fc : word) = Some W_609a4.
Proof. vm_refl. Qed.
Lemma D_609a4 : decode_any W_609a4 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609a8 : bv 32 := 0x00050413.
Lemma F_609a8 : fetch_word Plain.M.loaded_segments (0x60a00 : word) = Some W_609a8.
Proof. vm_refl. Qed.
Lemma D_609a8 : decode_any W_609a8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609ac : bv 32 := 0xfa0a2537.
Lemma F_609ac : fetch_word Plain.M.loaded_segments (0x60a04 : word) = Some W_609ac.
Proof. vm_refl. Qed.
Lemma D_609ac : decode_any W_609ac = Some (Lui 10 1024162, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609b0 : bv 32 := 0xeff50593.
Lemma F_609b0 : fetch_word Plain.M.loaded_segments (0x60a08 : word) = Some W_609b0.
Proof. vm_refl. Qed.
Lemma D_609b0 : decode_any W_609b0 = Some (OpImm ALU_ADD 11 10 3839, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609b4 : bv 32 := 0x00b405bb.
Lemma F_609b4 : fetch_word Plain.M.loaded_segments (0x60a0c : word) = Some W_609b4.
Proof. vm_refl. Qed.
Lemma D_609b4 : decode_any W_609b4 = Some (Op32 ALU_ADD 11 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609b8 : bv 32 := 0xf005051b.
Lemma F_609b8 : fetch_word Plain.M.loaded_segments (0x60a10 : word) = Some W_609b8.
Proof. vm_refl. Qed.
Lemma D_609b8 : decode_any W_609b8 = Some (OpImm32 10 10 3840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609bc : bv 32 := 0x00a5f463.
Lemma F_609bc : fetch_word Plain.M.loaded_segments (0x60a14 : word) = Some W_609bc.
Proof. vm_refl. Qed.
Lemma D_609bc : decode_any W_609bc = Some (Branch BC_GEU 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609c0 : bv 32 := 0x03200413.
Lemma F_609c0 : fetch_word Plain.M.loaded_segments (0x60a18 : word) = Some W_609c0.
Proof. vm_refl. Qed.
Lemma D_609c0 : decode_any W_609c0 = Some (OpImm ALU_ADD 8 0 50, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609c4 : bv 32 := 0x00100513.
Lemma F_609c4 : fetch_word Plain.M.loaded_segments (0x60a1c : word) = Some W_609c4.
Proof. vm_refl. Qed.
Lemma D_609c4 : decode_any W_609c4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609c8 : bv 32 := 0x02000593.
Lemma F_609c8 : fetch_word Plain.M.loaded_segments (0x60a20 : word) = Some W_609c8.
Proof. vm_refl. Qed.
Lemma D_609c8 : decode_any W_609c8 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609cc : bv 32 := 0x00100913.
Lemma F_609cc : fetch_word Plain.M.loaded_segments (0x60a24 : word) = Some W_609cc.
Proof. vm_refl. Qed.
Lemma D_609cc : decode_any W_609cc = Some (OpImm ALU_ADD 18 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609d0 : bv 32 := 0x6a5760ef.
Lemma F_609d0 : fetch_word Plain.M.loaded_segments (0x60a28 : word) = Some W_609d0.
Proof. vm_refl. Qed.
Lemma D_609d0 : decode_any W_609d0 = Some (Jal 1 487076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609d4 : bv 32 := 0x00050493.
Lemma F_609d4 : fetch_word Plain.M.loaded_segments (0x60a2c : word) = Some W_609d4.
Proof. vm_refl. Qed.
Lemma D_609d4 : decode_any W_609d4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609d8 : bv 32 := 0x00400593.
Lemma F_609d8 : fetch_word Plain.M.loaded_segments (0x60a30 : word) = Some W_609d8.
Proof. vm_refl. Qed.
Lemma D_609d8 : decode_any W_609d8 = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609dc : bv 32 := 0x00040513.
Lemma F_609dc : fetch_word Plain.M.loaded_segments (0x60a34 : word) = Some W_609dc.
Proof. vm_refl. Qed.
Lemma D_609dc : decode_any W_609dc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609e0 : bv 32 := 0x695760ef.
Lemma F_609e0 : fetch_word Plain.M.loaded_segments (0x60a38 : word) = Some W_609e0.
Proof. vm_refl. Qed.
Lemma D_609e0 : decode_any W_609e0 = Some (Jal 1 487060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609e4 : bv 32 := 0x00a4bc23.
Lemma F_609e4 : fetch_word Plain.M.loaded_segments (0x60a3c : word) = Some W_609e4.
Proof. vm_refl. Qed.
Lemma D_609e4 : decode_any W_609e4 = Some (Store SZ8 9 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609e8 : bv 32 := 0x02050463.
Lemma F_609e8 : fetch_word Plain.M.loaded_segments (0x60a40 : word) = Some W_609e8.
Proof. vm_refl. Qed.
Lemma D_609e8 : decode_any W_609e8 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609ec : bv 32 := 0x0084a023.
Lemma F_609ec : fetch_word Plain.M.loaded_segments (0x60a44 : word) = Some W_609ec.
Proof. vm_refl. Qed.
Lemma D_609ec : decode_any W_609ec = Some (Store SZ4 9 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609f0 : bv 32 := 0x0004a223.
Lemma F_609f0 : fetch_word Plain.M.loaded_segments (0x60a48 : word) = Some W_609f0.
Proof. vm_refl. Qed.
Lemma D_609f0 : decode_any W_609f0 = Some (Store SZ4 9 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609f4 : bv 32 := 0x0310000f.
Lemma F_609f4 : fetch_word Plain.M.loaded_segments (0x60a4c : word) = Some W_609f4.
Proof. vm_refl. Qed.
Lemma D_609f4 : decode_any W_609f4 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609f8 : bv 32 := 0x0124a423.
Lemma F_609f8 : fetch_word Plain.M.loaded_segments (0x60a50 : word) = Some W_609f8.
Proof. vm_refl. Qed.
Lemma D_609f8 : decode_any W_609f8 = Some (Store SZ4 9 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609fc : bv 32 := 0x0330000f.
Lemma F_609fc : fetch_word Plain.M.loaded_segments (0x60a54 : word) = Some W_609fc.
Proof. vm_refl. Qed.
Lemma D_609fc : decode_any W_609fc = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a00 : bv 32 := 0x3f8005b7.
Lemma F_60a00 : fetch_word Plain.M.loaded_segments (0x60a58 : word) = Some W_60a00.
Proof. vm_refl. Qed.
Lemma D_60a00 : decode_any W_60a00 = Some (Lui 11 260096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a04 : bv 32 := 0x0004a623.
Lemma F_60a04 : fetch_word Plain.M.loaded_segments (0x60a5c : word) = Some W_60a04.
Proof. vm_refl. Qed.
Lemma D_60a04 : decode_any W_60a04 = Some (Store SZ4 9 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a08 : bv 32 := 0x00b4a823.
Lemma F_60a08 : fetch_word Plain.M.loaded_segments (0x60a60 : word) = Some W_60a08.
Proof. vm_refl. Qed.
Lemma D_60a08 : decode_any W_60a08 = Some (Store SZ4 9 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a0c : bv 32 := 0x0700006f.
Lemma F_60a0c : fetch_word Plain.M.loaded_segments (0x60a64 : word) = Some W_60a0c.
Proof. vm_refl. Qed.
Lemma D_60a0c : decode_any W_60a0c = Some (Jal 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a7c : bv 32 := 0x00048513.
Lemma F_60a7c : fetch_word Plain.M.loaded_segments (0x60ad4 : word) = Some W_60a7c.
Proof. vm_refl. Qed.
Lemma D_60a7c : decode_any W_60a7c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a80 : bv 32 := 0x01813083.
Lemma F_60a80 : fetch_word Plain.M.loaded_segments (0x60ad8 : word) = Some W_60a80.
Proof. vm_refl. Qed.
Lemma D_60a80 : decode_any W_60a80 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a84 : bv 32 := 0x01013403.
Lemma F_60a84 : fetch_word Plain.M.loaded_segments (0x60adc : word) = Some W_60a84.
Proof. vm_refl. Qed.
Lemma D_60a84 : decode_any W_60a84 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a88 : bv 32 := 0x00813483.
Lemma F_60a88 : fetch_word Plain.M.loaded_segments (0x60ae0 : word) = Some W_60a88.
Proof. vm_refl. Qed.
Lemma D_60a88 : decode_any W_60a88 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a8c : bv 32 := 0x00013903.
Lemma F_60a8c : fetch_word Plain.M.loaded_segments (0x60ae4 : word) = Some W_60a8c.
Proof. vm_refl. Qed.
Lemma D_60a8c : decode_any W_60a8c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a90 : bv 32 := 0x02010113.
Lemma F_60a90 : fetch_word Plain.M.loaded_segments (0x60ae8 : word) = Some W_60a90.
Proof. vm_refl. Qed.
Lemma D_60a90 : decode_any W_60a90 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a94 : bv 32 := 0x00008067.
Lemma F_60a94 : fetch_word Plain.M.loaded_segments (0x60aec : word) = Some W_60a94.
Proof. vm_refl. Qed.
Lemma D_60a94 : decode_any W_60a94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a98 : bv 32 := 0xfe010113.
Lemma F_60a98 : fetch_word Plain.M.loaded_segments (0x60af0 : word) = Some W_60a98.
Proof. vm_refl. Qed.
Lemma D_60a98 : decode_any W_60a98 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a9c : bv 32 := 0x00113c23.
Lemma F_60a9c : fetch_word Plain.M.loaded_segments (0x60af4 : word) = Some W_60a9c.
Proof. vm_refl. Qed.
Lemma D_60a9c : decode_any W_60a9c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60aa0 : bv 32 := 0x00813823.
Lemma F_60aa0 : fetch_word Plain.M.loaded_segments (0x60af8 : word) = Some W_60aa0.
Proof. vm_refl. Qed.
Lemma D_60aa0 : decode_any W_60aa0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60aa4 : bv 32 := 0x00913423.
Lemma F_60aa4 : fetch_word Plain.M.loaded_segments (0x60afc : word) = Some W_60aa4.
Proof. vm_refl. Qed.
Lemma D_60aa4 : decode_any W_60aa4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60aa8 : bv 32 := 0x04050263.
Lemma F_60aa8 : fetch_word Plain.M.loaded_segments (0x60b00 : word) = Some W_60aa8.
Proof. vm_refl. Qed.
Lemma D_60aa8 : decode_any W_60aa8 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60aac : bv 32 := 0x00053403.
Lemma F_60aac : fetch_word Plain.M.loaded_segments (0x60b04 : word) = Some W_60aac.
Proof. vm_refl. Qed.
Lemma D_60aac : decode_any W_60aac = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ab0 : bv 32 := 0x06040a63.
Lemma F_60ab0 : fetch_word Plain.M.loaded_segments (0x60b08 : word) = Some W_60ab0.
Proof. vm_refl. Qed.
Lemma D_60ab0 : decode_any W_60ab0 = Some (Branch BC_EQ 8 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ab4 : bv 32 := 0x00840593.
Lemma F_60ab4 : fetch_word Plain.M.loaded_segments (0x60b0c : word) = Some W_60ab4.
Proof. vm_refl. Qed.
Lemma D_60ab4 : decode_any W_60ab4 = Some (OpImm ALU_ADD 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ab8 : bv 32 := 0xfff00613.
Lemma F_60ab8 : fetch_word Plain.M.loaded_segments (0x60b10 : word) = Some W_60ab8.
Proof. vm_refl. Qed.
Lemma D_60ab8 : decode_any W_60ab8 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60abc : bv 32 := 0x06c5a5af.
Lemma F_60abc : fetch_word Plain.M.loaded_segments (0x60b14 : word) = Some W_60abc.
Proof. vm_refl. Qed.
Lemma D_60abc : decode_any W_60abc = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ac0 : bv 32 := 0x00100613.
Lemma F_60ac0 : fetch_word Plain.M.loaded_segments (0x60b18 : word) = Some W_60ac0.
Proof. vm_refl. Qed.
Lemma D_60ac0 : decode_any W_60ac0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ac4 : bv 32 := 0x02c59063.
Lemma F_60ac4 : fetch_word Plain.M.loaded_segments (0x60b1c : word) = Some W_60ac4.
Proof. vm_refl. Qed.
Lemma D_60ac4 : decode_any W_60ac4 = Some (Branch BC_NE 11 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ac8 : bv 32 := 0x00050493.
Lemma F_60ac8 : fetch_word Plain.M.loaded_segments (0x60b20 : word) = Some W_60ac8.
Proof. vm_refl. Qed.
Lemma D_60ac8 : decode_any W_60ac8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60acc : bv 32 := 0x01843503.
Lemma F_60acc : fetch_word Plain.M.loaded_segments (0x60b24 : word) = Some W_60acc.
Proof. vm_refl. Qed.
Lemma D_60acc : decode_any W_60acc = Some (Load SZ8 true 10 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ad0 : bv 32 := 0x00050463.
Lemma F_60ad0 : fetch_word Plain.M.loaded_segments (0x60b28 : word) = Some W_60ad0.
Proof. vm_refl. Qed.
Lemma D_60ad0 : decode_any W_60ad0 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ad4 : bv 32 := 0x6d9760ef.
Lemma F_60ad4 : fetch_word Plain.M.loaded_segments (0x60b2c : word) = Some W_60ad4.
Proof. vm_refl. Qed.
Lemma D_60ad4 : decode_any W_60ad4 = Some (Jal 1 487128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ad8 : bv 32 := 0x00040513.
Lemma F_60ad8 : fetch_word Plain.M.loaded_segments (0x60b30 : word) = Some W_60ad8.
Proof. vm_refl. Qed.
Lemma D_60ad8 : decode_any W_60ad8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60adc : bv 32 := 0x6d1760ef.
Lemma F_60adc : fetch_word Plain.M.loaded_segments (0x60b34 : word) = Some W_60adc.
Proof. vm_refl. Qed.
Lemma D_60adc : decode_any W_60adc = Some (Jal 1 487120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ae0 : bv 32 := 0x00048513.
Lemma F_60ae0 : fetch_word Plain.M.loaded_segments (0x60b38 : word) = Some W_60ae0.
Proof. vm_refl. Qed.
Lemma D_60ae0 : decode_any W_60ae0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ae4 : bv 32 := 0x00053023.
Lemma F_60ae4 : fetch_word Plain.M.loaded_segments (0x60b3c : word) = Some W_60ae4.
Proof. vm_refl. Qed.
Lemma D_60ae4 : decode_any W_60ae4 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ae8 : bv 32 := 0x03c0006f.
Lemma F_60ae8 : fetch_word Plain.M.loaded_segments (0x60b40 : word) = Some W_60ae8.
Proof. vm_refl. Qed.
Lemma D_60ae8 : decode_any W_60ae8 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b24 : bv 32 := 0x01813083.
Lemma F_60b24 : fetch_word Plain.M.loaded_segments (0x60b7c : word) = Some W_60b24.
Proof. vm_refl. Qed.
Lemma D_60b24 : decode_any W_60b24 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b28 : bv 32 := 0x01013403.
Lemma F_60b28 : fetch_word Plain.M.loaded_segments (0x60b80 : word) = Some W_60b28.
Proof. vm_refl. Qed.
Lemma D_60b28 : decode_any W_60b28 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b2c : bv 32 := 0x00813483.
Lemma F_60b2c : fetch_word Plain.M.loaded_segments (0x60b84 : word) = Some W_60b2c.
Proof. vm_refl. Qed.
Lemma D_60b2c : decode_any W_60b2c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b30 : bv 32 := 0x02010113.
Lemma F_60b30 : fetch_word Plain.M.loaded_segments (0x60b88 : word) = Some W_60b30.
Proof. vm_refl. Qed.
Lemma D_60b30 : decode_any W_60b30 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b34 : bv 32 := 0x00008067.
Lemma F_60b34 : fetch_word Plain.M.loaded_segments (0x60b8c : word) = Some W_60b34.
Proof. vm_refl. Qed.
Lemma D_60b34 : decode_any W_60b34 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b38 : bv 32 := 0xfe010113.
Lemma F_60b38 : fetch_word Plain.M.loaded_segments (0x60b90 : word) = Some W_60b38.
Proof. vm_refl. Qed.
Lemma D_60b38 : decode_any W_60b38 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b3c : bv 32 := 0x00113c23.
Lemma F_60b3c : fetch_word Plain.M.loaded_segments (0x60b94 : word) = Some W_60b3c.
Proof. vm_refl. Qed.
Lemma D_60b3c : decode_any W_60b3c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b40 : bv 32 := 0x00813823.
Lemma F_60b40 : fetch_word Plain.M.loaded_segments (0x60b98 : word) = Some W_60b40.
Proof. vm_refl. Qed.
Lemma D_60b40 : decode_any W_60b40 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b44 : bv 32 := 0x00913423.
Lemma F_60b44 : fetch_word Plain.M.loaded_segments (0x60b9c : word) = Some W_60b44.
Proof. vm_refl. Qed.
Lemma D_60b44 : decode_any W_60b44 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b48 : bv 32 := 0x00813027.
Lemma F_60b48 : fetch_word Plain.M.loaded_segments (0x60ba0 : word) = Some W_60b48.
Proof. vm_refl. Qed.
Lemma D_60b48 : decode_any W_60b48 = Some (FStore FMT_D 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b4c : bv 32 := 0x04050663.
Lemma F_60b4c : fetch_word Plain.M.loaded_segments (0x60ba4 : word) = Some W_60b4c.
Proof. vm_refl. Qed.
Lemma D_60b4c : decode_any W_60b4c = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b50 : bv 32 := 0x00052583.
Lemma F_60b50 : fetch_word Plain.M.loaded_segments (0x60ba8 : word) = Some W_60b50.
Proof. vm_refl. Qed.
Lemma D_60b50 : decode_any W_60b50 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b54 : bv 32 := 0x00452403.
Lemma F_60b54 : fetch_word Plain.M.loaded_segments (0x60bac : word) = Some W_60b54.
Proof. vm_refl. Qed.
Lemma D_60b54 : decode_any W_60b54 = Some (Load SZ4 true 8 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b58 : bv 32 := 0x00040613.
Lemma F_60b58 : fetch_word Plain.M.loaded_segments (0x60bb0 : word) = Some W_60b58.
Proof. vm_refl. Qed.
Lemma D_60b58 : decode_any W_60b58 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b5c : bv 32 := 0x08b44863.
Lemma F_60b5c : fetch_word Plain.M.loaded_segments (0x60bb4 : word) = Some W_60b5c.
Proof. vm_refl. Qed.
Lemma D_60b5c : decode_any W_60b5c = Some (Branch BC_LT 8 11 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b60 : bv 32 := 0x20a50453.
Lemma F_60b60 : fetch_word Plain.M.loaded_segments (0x60bb8 : word) = Some W_60b60.
Proof. vm_refl. Qed.
Lemma D_60b60 : decode_any W_60b60 = Some (Fsgnj F_SGNJ FMT_S 8 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b64 : bv 32 := 0x00050493.
Lemma F_60b64 : fetch_word Plain.M.loaded_segments (0x60bbc : word) = Some W_60b64.
Proof. vm_refl. Qed.
Lemma D_60b64 : decode_any W_60b64 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b68 : bv 32 := 0x0fc000ef.
Lemma F_60b68 : fetch_word Plain.M.loaded_segments (0x60bc0 : word) = Some W_60b68.
Proof. vm_refl. Qed.
Lemma D_60b68 : decode_any W_60b68 = Some (Jal 1 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b6c : bv 32 := 0x06050a63.
Lemma F_60b6c : fetch_word Plain.M.loaded_segments (0x60bc4 : word) = Some W_60b6c.
Proof. vm_refl. Qed.
Lemma D_60b6c : decode_any W_60b6c = Some (Branch BC_EQ 10 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60be0 : bv 32 := 0x00048513.
Lemma F_60be0 : fetch_word Plain.M.loaded_segments (0x60c38 : word) = Some W_60be0.
Proof. vm_refl. Qed.
Lemma D_60be0 : decode_any W_60be0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60be4 : bv 32 := 0x0044a603.
Lemma F_60be4 : fetch_word Plain.M.loaded_segments (0x60c3c : word) = Some W_60be4.
Proof. vm_refl. Qed.
Lemma D_60be4 : decode_any W_60be4 = Some (Load SZ4 true 12 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60be8 : bv 32 := 0x20840553.
Lemma F_60be8 : fetch_word Plain.M.loaded_segments (0x60c40 : word) = Some W_60be8.
Proof. vm_refl. Qed.
Lemma D_60be8 : decode_any W_60be8 = Some (Fsgnj F_SGNJ FMT_S 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bec : bv 32 := 0x00000593.
Lemma F_60bec : fetch_word Plain.M.loaded_segments (0x60c44 : word) = Some W_60bec.
Proof. vm_refl. Qed.
Lemma D_60bec : decode_any W_60bec = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bf0 : bv 32 := 0x01853683.
Lemma F_60bf0 : fetch_word Plain.M.loaded_segments (0x60c48 : word) = Some W_60bf0.
Proof. vm_refl. Qed.
Lemma D_60bf0 : decode_any W_60bf0 = Some (Load SZ8 true 13 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bf4 : bv 32 := 0x00241413.
Lemma F_60bf4 : fetch_word Plain.M.loaded_segments (0x60c4c : word) = Some W_60bf4.
Proof. vm_refl. Qed.
Lemma D_60bf4 : decode_any W_60bf4 = Some (ShiftImm ALU_SLL 8 8 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bf8 : bv 32 := 0x008686b3.
Lemma F_60bf8 : fetch_word Plain.M.loaded_segments (0x60c50 : word) = Some W_60bf8.
Proof. vm_refl. Qed.
Lemma D_60bf8 : decode_any W_60bf8 = Some (Op ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bfc : bv 32 := 0x00160613.
Lemma F_60bfc : fetch_word Plain.M.loaded_segments (0x60c54 : word) = Some W_60bfc.
Proof. vm_refl. Qed.
Lemma D_60bfc : decode_any W_60bfc = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c00 : bv 32 := 0x00a6a027.
Lemma F_60c00 : fetch_word Plain.M.loaded_segments (0x60c58 : word) = Some W_60c00.
Proof. vm_refl. Qed.
Lemma D_60c00 : decode_any W_60c00 = Some (FStore FMT_S 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c04 : bv 32 := 0x00c52223.
Lemma F_60c04 : fetch_word Plain.M.loaded_segments (0x60c5c : word) = Some W_60c04.
Proof. vm_refl. Qed.
Lemma D_60c04 : decode_any W_60c04 = Some (Store SZ4 10 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c08 : bv 32 := 0x00058513.
Lemma F_60c08 : fetch_word Plain.M.loaded_segments (0x60c60 : word) = Some W_60c08.
Proof. vm_refl. Qed.
Lemma D_60c08 : decode_any W_60c08 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c0c : bv 32 := 0x01813083.
Lemma F_60c0c : fetch_word Plain.M.loaded_segments (0x60c64 : word) = Some W_60c0c.
Proof. vm_refl. Qed.
Lemma D_60c0c : decode_any W_60c0c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c10 : bv 32 := 0x01013403.
Lemma F_60c10 : fetch_word Plain.M.loaded_segments (0x60c68 : word) = Some W_60c10.
Proof. vm_refl. Qed.
Lemma D_60c10 : decode_any W_60c10 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c14 : bv 32 := 0x00813483.
Lemma F_60c14 : fetch_word Plain.M.loaded_segments (0x60c6c : word) = Some W_60c14.
Proof. vm_refl. Qed.
Lemma D_60c14 : decode_any W_60c14 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c18 : bv 32 := 0x00013407.
Lemma F_60c18 : fetch_word Plain.M.loaded_segments (0x60c70 : word) = Some W_60c18.
Proof. vm_refl. Qed.
Lemma D_60c18 : decode_any W_60c18 = Some (FLoad FMT_D 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c1c : bv 32 := 0x02010113.
Lemma F_60c1c : fetch_word Plain.M.loaded_segments (0x60c74 : word) = Some W_60c1c.
Proof. vm_refl. Qed.
Lemma D_60c1c : decode_any W_60c1c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c20 : bv 32 := 0x00008067.
Lemma F_60c20 : fetch_word Plain.M.loaded_segments (0x60c78 : word) = Some W_60c20.
Proof. vm_refl. Qed.
Lemma D_60c20 : decode_any W_60c20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c64 : bv 32 := 0xff010113.
Lemma F_60c64 : fetch_word Plain.M.loaded_segments (0x60cbc : word) = Some W_60c64.
Proof. vm_refl. Qed.
Lemma D_60c64 : decode_any W_60c64 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c68 : bv 32 := 0x00113423.
Lemma F_60c68 : fetch_word Plain.M.loaded_segments (0x60cc0 : word) = Some W_60c68.
Proof. vm_refl. Qed.
Lemma D_60c68 : decode_any W_60c68 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c6c : bv 32 := 0x00813023.
Lemma F_60c6c : fetch_word Plain.M.loaded_segments (0x60cc4 : word) = Some W_60c6c.
Proof. vm_refl. Qed.
Lemma D_60c6c : decode_any W_60c6c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c70 : bv 32 := 0x00056603.
Lemma F_60c70 : fetch_word Plain.M.loaded_segments (0x60cc8 : word) = Some W_60c70.
Proof. vm_refl. Qed.
Lemma D_60c70 : decode_any W_60c70 = Some (Load SZ4 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c74 : bv 32 := 0x05f5e5b7.
Lemma F_60c74 : fetch_word Plain.M.loaded_segments (0x60ccc : word) = Some W_60c74.
Proof. vm_refl. Qed.
Lemma D_60c74 : decode_any W_60c74 = Some (Lui 11 24414, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c78 : bv 32 := 0x1015859b.
Lemma F_60c78 : fetch_word Plain.M.loaded_segments (0x60cd0 : word) = Some W_60c78.
Proof. vm_refl. Qed.
Lemma D_60c78 : decode_any W_60c78 = Some (OpImm32 11 11 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c7c : bv 32 := 0x02b66663.
Lemma F_60c7c : fetch_word Plain.M.loaded_segments (0x60cd4 : word) = Some W_60c7c.
Proof. vm_refl. Qed.
Lemma D_60c7c : decode_any W_60c7c = Some (Branch BC_LTU 12 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ca8 : bv 32 := 0x02faf5b7.
Lemma F_60ca8 : fetch_word Plain.M.loaded_segments (0x60d00 : word) = Some W_60ca8.
Proof. vm_refl. Qed.
Lemma D_60ca8 : decode_any W_60ca8 = Some (Lui 11 12207, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cac : bv 32 := 0x0815859b.
Lemma F_60cac : fetch_word Plain.M.loaded_segments (0x60d04 : word) = Some W_60cac.
Proof. vm_refl. Qed.
Lemma D_60cac : decode_any W_60cac = Some (OpImm32 11 11 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cb0 : bv 32 := 0x02b66663.
Lemma F_60cb0 : fetch_word Plain.M.loaded_segments (0x60d08 : word) = Some W_60cb0.
Proof. vm_refl. Qed.
Lemma D_60cb0 : decode_any W_60cb0 = Some (Branch BC_LTU 12 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cdc : bv 32 := 0x00261593.
Lemma F_60cdc : fetch_word Plain.M.loaded_segments (0x60d34 : word) = Some W_60cdc.
Proof. vm_refl. Qed.
Lemma D_60cdc : decode_any W_60cdc = Some (ShiftImm ALU_SLL 11 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ce0 : bv 32 := 0x00361613.
Lemma F_60ce0 : fetch_word Plain.M.loaded_segments (0x60d38 : word) = Some W_60ce0.
Proof. vm_refl. Qed.
Lemma D_60ce0 : decode_any W_60ce0 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ce4 : bv 32 := 0x01850693.
Lemma F_60ce4 : fetch_word Plain.M.loaded_segments (0x60d3c : word) = Some W_60ce4.
Proof. vm_refl. Qed.
Lemma D_60ce4 : decode_any W_60ce4 = Some (OpImm ALU_ADD 13 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ce8 : bv 32 := 0x00050413.
Lemma F_60ce8 : fetch_word Plain.M.loaded_segments (0x60d40 : word) = Some W_60ce8.
Proof. vm_refl. Qed.
Lemma D_60ce8 : decode_any W_60ce8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cec : bv 32 := 0x00068513.
Lemma F_60cec : fetch_word Plain.M.loaded_segments (0x60d44 : word) = Some W_60cec.
Proof. vm_refl. Qed.
Lemma D_60cec : decode_any W_60cec = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cf0 : bv 32 := 0xeddfc0ef.
Lemma F_60cf0 : fetch_word Plain.M.loaded_segments (0x60d48 : word) = Some W_60cf0.
Proof. vm_refl. Qed.
Lemma D_60cf0 : decode_any W_60cf0 = Some (Jal 1 2084572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cf4 : bv 32 := 0x00a43c23.
Lemma F_60cf4 : fetch_word Plain.M.loaded_segments (0x60d4c : word) = Some W_60cf4.
Proof. vm_refl. Qed.
Lemma D_60cf4 : decode_any W_60cf4 = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cf8 : bv 32 := 0x00050c63.
Lemma F_60cf8 : fetch_word Plain.M.loaded_segments (0x60d50 : word) = Some W_60cf8.
Proof. vm_refl. Qed.
Lemma D_60cf8 : decode_any W_60cf8 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cfc : bv 32 := 0x00000513.
Lemma F_60cfc : fetch_word Plain.M.loaded_segments (0x60d54 : word) = Some W_60cfc.
Proof. vm_refl. Qed.
Lemma D_60cfc : decode_any W_60cfc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d00 : bv 32 := 0x00042603.
Lemma F_60d00 : fetch_word Plain.M.loaded_segments (0x60d58 : word) = Some W_60d00.
Proof. vm_refl. Qed.
Lemma D_60d00 : decode_any W_60d00 = Some (Load SZ4 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d04 : bv 32 := 0x00161613.
Lemma F_60d04 : fetch_word Plain.M.loaded_segments (0x60d5c : word) = Some W_60d04.
Proof. vm_refl. Qed.
Lemma D_60d04 : decode_any W_60d04 = Some (ShiftImm ALU_SLL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d08 : bv 32 := 0x00c42023.
Lemma F_60d08 : fetch_word Plain.M.loaded_segments (0x60d60 : word) = Some W_60d08.
Proof. vm_refl. Qed.
Lemma D_60d08 : decode_any W_60d08 = Some (Store SZ4 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d0c : bv 32 := 0x0400006f.
Lemma F_60d0c : fetch_word Plain.M.loaded_segments (0x60d64 : word) = Some W_60d0c.
Proof. vm_refl. Qed.
Lemma D_60d0c : decode_any W_60d0c = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d4c : bv 32 := 0x00813083.
Lemma F_60d4c : fetch_word Plain.M.loaded_segments (0x60da4 : word) = Some W_60d4c.
Proof. vm_refl. Qed.
Lemma D_60d4c : decode_any W_60d4c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d50 : bv 32 := 0x00013403.
Lemma F_60d50 : fetch_word Plain.M.loaded_segments (0x60da8 : word) = Some W_60d50.
Proof. vm_refl. Qed.
Lemma D_60d50 : decode_any W_60d50 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d54 : bv 32 := 0x01010113.
Lemma F_60d54 : fetch_word Plain.M.loaded_segments (0x60dac : word) = Some W_60d54.
Proof. vm_refl. Qed.
Lemma D_60d54 : decode_any W_60d54 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d58 : bv 32 := 0x00008067.
Lemma F_60d58 : fetch_word Plain.M.loaded_segments (0x60db0 : word) = Some W_60d58.
Proof. vm_refl. Qed.
Lemma D_60d58 : decode_any W_60d58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

