From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YO0i.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition KRES : Z := 8.
(* The occupied-bytes budget: reserved entries (<= 2^30) plus live mappings (<= MG_LIVE = 2^45). *)
Definition SLOT_BYTES : Z := 2 ^ 45 + 2 ^ 30.
(* 08b1429: a grant is Linux's own address, which (for a hint of 0) lands in Linux's bottom-up
   window [task_unmapped_base, alloc_top).  The model's floor is Sys/Mm/Mmap.v's task_unmapped_base
   = 0x2aaaaab000, Linux 6.18 arch/riscv/include/asm/processor.h:52 TASK_UNMAPPED_BASE =
   PAGE_ALIGN((1 << MMAP_MIN_VA_BITS) / 3) with MMAP_MIN_VA_BITS = 39.  So the slot budget is the
   window [MMAP_FLOOR, CEIL_MIN) less the occupied bytes, shared among one gap per obstacle. *)
Definition MMAP_FLOOR : Z := LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.task_unmapped_base.
Lemma MMAP_FLOOR_eq : MMAP_FLOOR = 183251939328.
Proof. reflexivity. Qed.
Definition slot_cap (R : Z) : Z := (CEIL_MIN - MMAP_FLOOR - SLOT_BYTES) / (page_round R + PGSZ) - 1.
Lemma slot_round_ge : forall R, R <= page_round R.
Proof.
intros R. unfold page_round, PGSZ.
pose proof (Z_div_mod_eq_full (R + 4096 - 1) 4096).
pose proof (Z.mod_pos_bound (R + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.
Lemma slot_round_mono : forall R1 R2, R1 <= R2 -> page_round R1 <= page_round R2.
Proof.
intros R1 R2 H. unfold page_round, PGSZ.
pose proof (Z.div_le_mono (R1 + 4096 - 1) (R2 + 4096 - 1) 4096 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma slot_cap_anti : forall R1 R2, 0 < R1 <= R2 -> slot_cap R2 <= slot_cap R1.
Proof.
intros R1 R2 H. unfold slot_cap.
pose proof (slot_round_ge R1). pose proof (slot_round_mono R1 R2 ltac:(lia)).
assert (D : (CEIL_MIN - MMAP_FLOOR - SLOT_BYTES) / (page_round R2 + PGSZ) <= (CEIL_MIN - MMAP_FLOOR - SLOT_BYTES) / (page_round R1 + PGSZ)).
{ apply Z.div_le_compat_l; [rewrite MMAP_FLOOR_eq; unfold SLOT_BYTES; lia | unfold PGSZ; lia]. }
lia.
Qed.
