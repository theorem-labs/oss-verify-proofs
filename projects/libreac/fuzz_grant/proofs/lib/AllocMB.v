From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YO0i YO0f YO0j YO0m.
Local Open Scope Z_scope.

Definition MB (s : astate) : Prop := brk_bytes s <= PGSZ * (nareas s + 1) /\ resv_count s <= shift s.

Lemma MB_init : MB init_state.
Proof. unfold MB, brk_bytes, resv_count, nareas, shift. cbn. unfold PGSZ. lia. Qed.
