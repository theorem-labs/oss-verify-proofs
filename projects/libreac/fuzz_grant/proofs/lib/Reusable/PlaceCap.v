From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YO0i.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition KRES : Z := 8.
Definition SLOT_BYTES : Z := 2 ^ 45 + 2 ^ 30.
Definition slot_cap (R : Z) : Z := (CEIL_MIN - SLOT_BYTES) / (page_round R + PGSZ) - 1.
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
assert (D : (CEIL_MIN - SLOT_BYTES) / (page_round R2 + PGSZ) <= (CEIL_MIN - SLOT_BYTES) / (page_round R1 + PGSZ)).
{ apply Z.div_le_compat_l; [unfold SLOT_BYTES; lia | unfold PGSZ; lia]. }
lia.
Qed.
