From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YO0i.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YO03.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import AllocSlots.
Local Open Scope Z_scope.

Definition NONHEAP_CF : Z := 2 ^ 31.

Definition room_cf (md : Model) (b : sbound) (n : Z) : Prop :=
  room_slots b n /\ LIVE_BOUND (sb_cap b) (sb_bytes b + n) + NONHEAP_CF <= vm_limit (m_vmmaps md).

Lemma LIVE_BOUND_mono : forall c c' y y', 0 <= c <= c' -> y <= y' -> LIVE_BOUND c y <= LIVE_BOUND c' y'.
Proof.
  intros c c' y y' Hc Hy. unfold LIVE_BOUND, AREA_BOUND, P2, NA, HCAP.
  assert (D : (13 * c + 48) / METAS_PER_AREA <= (13 * c' + 48) / METAS_PER_AREA)
    by (apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | lia]).
  unfold OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.YO03.MMAX, PGSZ in *. nia.
Qed.

Lemma room_cf_of_bound : forall X Y md b n, LIVE_BOUND X Y + NONHEAP_CF <= vm_limit (m_vmmaps md) ->
  room_slots b n -> 0 <= sb_cap b <= X -> sb_bytes b + n <= Y -> room_cf md b n.
Proof.
  intros X Y md b n Hl Hr Hc Hb. split; [exact Hr|].
  pose proof (LIVE_BOUND_mono (sb_cap b) X (sb_bytes b + n) Y Hc Hb). lia.
Qed.
