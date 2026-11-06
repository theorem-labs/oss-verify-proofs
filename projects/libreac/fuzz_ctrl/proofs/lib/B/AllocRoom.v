From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YO0i YO0d YO03 YO0o PlaceCap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AllocSlots.
Local Open Scope Z_scope.

Lemma RQ_BOUND_mono c c' n n' : c' <= c -> n' <= n -> 0 < RQ_BOUND c' n' <= RQ_BOUND c n.
Proof.
  intros Hc Hn.
  assert (D : HCAP c' / METAS_PER_AREA <= HCAP c / METAS_PER_AREA) by (apply Z.div_le_mono; unfold HCAP, METAS_PER_AREA; lia).
  pose proof (page_round_mono (n' + IB + UNIT) (n + IB + UNIT) ltac:(lia)) as P.
  unfold RQ_BOUND, AREA_BOUND, P2 in *. change MMAX with 8388608. unfold PGSZ. lia.
Qed.

Lemma CAPOK_mono : forall c c' B B' n n', c' <= c -> B' <= B -> 0 <= n' <= n -> CAPOK c B n -> CAPOK c' B' n'.
Proof.
  intros c c' B B' n n' Hc HB Hn (C1 & C2 & C3 & C4).
  assert (HH : HCAP c' <= HCAP c) by (unfold HCAP; lia).
  assert (D : HCAP c' / METAS_PER_AREA <= HCAP c / METAS_PER_AREA) by (apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | exact HH]).
  pose proof (page_round_mono (n' + IB + UNIT) (n + IB + UNIT) ltac:(lia)) as P.
  pose proof (RQ_BOUND_mono c c' n n' ltac:(lia) ltac:(lia)) as [R0 R].
  pose proof (slot_cap_anti _ _ (conj R0 R)) as SC.
  unfold CAPOK. split; [|split; [|split]].
  - unfold LIVE_BOUND, AREA_BOUND, NA, P2 in *. change MMAX with 8388608 in *. unfold PGSZ in *. lia.
  - unfold SLOTS_BOUND, NA in *. lia.
  - lia.
  - lia.
Qed.

Definition CAPMAX : Z := 296960.

Definition CAP29 : Z := 174080.

Definition CAP30 : Z := 86016.

Lemma CAPOK_small : CAPOK CAPMAX (2 ^ 40) (2 ^ 22).
Proof. unfold CAPOK. split; [|split; [|split]]; first [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. Qed.

Lemma CAPOK_big : CAPOK CAPMAX (2 ^ 40) (2 ^ 28 - 2 ^ 13).
Proof. unfold CAPOK. split; [|split; [|split]]; first [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. Qed.

Lemma CAPOK_huge : CAPOK CAP29 (2 ^ 40) (2 ^ 29 + 2 ^ 13).
Proof. unfold CAPOK. split; [|split; [|split]]; first [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. Qed.

Lemma CAPOK_giant : CAPOK CAP30 (2 ^ 40) (2 ^ 30 - 2 ^ 13).
Proof. unfold CAPOK. split; [|split; [|split]]; first [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. Qed.

Theorem room_slots_small : forall b n, 0 <= n <= 2 ^ 22 -> sb_live b + 1 <= sb_cap b <= CAPMAX ->
  0 <= sb_bytes b -> sb_bytes b + n <= 2 ^ 40 -> room_slots b n.
Proof.
  intros b n Hn Hc Hb Hbn. unfold room_slots. split; [lia|]. split; [lia|].
  apply (CAPOK_mono CAPMAX (sb_cap b) (2 ^ 40) (sb_bytes b + n) (2 ^ 22) n); [lia | exact Hbn | lia | exact CAPOK_small].
Qed.

Theorem room_slots_big : forall b n, 0 <= n <= 2 ^ 28 - 2 ^ 13 -> sb_live b + 1 <= sb_cap b <= CAPMAX ->
  0 <= sb_bytes b -> sb_bytes b + n <= 2 ^ 40 -> room_slots b n.
Proof.
  intros b n Hn Hc Hb Hbn. unfold room_slots. split; [lia|]. split; [lia|].
  apply (CAPOK_mono CAPMAX (sb_cap b) (2 ^ 40) (sb_bytes b + n) (2 ^ 28 - 2 ^ 13) n); [lia | exact Hbn | lia | exact CAPOK_big].
Qed.

Theorem room_slots_huge : forall b n, 0 <= n <= 2 ^ 29 + 2 ^ 13 -> sb_live b + 1 <= sb_cap b <= CAP29 ->
  0 <= sb_bytes b -> sb_bytes b + n <= 2 ^ 40 -> room_slots b n.
Proof.
  intros b n Hn Hc Hb Hbn. unfold room_slots. split; [lia|]. split; [lia|].
  apply (CAPOK_mono CAP29 (sb_cap b) (2 ^ 40) (sb_bytes b + n) (2 ^ 29 + 2 ^ 13) n); [lia | exact Hbn | lia | exact CAPOK_huge].
Qed.

Theorem room_slots_giant : forall b n, 0 <= n <= 2 ^ 30 - 2 ^ 13 -> sb_live b + 1 <= sb_cap b <= CAP30 ->
  0 <= sb_bytes b -> sb_bytes b + n <= 2 ^ 40 -> room_slots b n.
Proof.
  intros b n Hn Hc Hb Hbn. unfold room_slots. split; [lia|]. split; [lia|].
  apply (CAPOK_mono CAP30 (sb_cap b) (2 ^ 40) (sb_bytes b + n) (2 ^ 30 - 2 ^ 13) n); [lia | exact Hbn | lia | exact CAPOK_giant].
Qed.
