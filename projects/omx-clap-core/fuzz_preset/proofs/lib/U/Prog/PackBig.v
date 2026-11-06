From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO03 PlaceCap.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocPack AllocPackRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PackFit PackOwn PackVec.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pb_capok : forall H M, 0 <= H -> M + H / 101 <= 167052 -> H <= 988596 -> CAPOK2 H M pq_BMAX pq_NMAX.
Proof.
  intros H M H0 H1 H2.
  assert (Hg : 0 <= H / 101) by (apply Z.div_pos; lia).
  assert (Hg2 : H / 101 <= 9789) by (apply Z.div_le_upper_bound; lia).
  assert (P : page_round (pq_NMAX + IB + UNIT) = 536866816) by (vm_compute; reflexivity).
  assert (EM : MMAX = 8388608) by reflexivity.
  assert (R : RQ2 H pq_NMAX = 536866816).
  { unfold RQ2, AREA2. rewrite P, EM. unfold METAS_PER_AREA, PGSZ. set (g := H / 101) in *. lia. }
  assert (S : 167107 <= slot_cap 536866816) by (apply Z.leb_le; vm_compute; reflexivity).
  unfold CAPOK2. rewrite R, P.
  unfold LIVE2, SLOTS2, NA2, AREA2, METAS_PER_AREA, PGSZ, KRES.
  rewrite EM.
  assert (EL : MG_LIVE = 35184372088832) by reflexivity.
  assert (ER : MG_REQ = 1073741824) by reflexivity.
  assert (EB : pq_BMAX = 17592186044416) by reflexivity.
  assert (E40 : 2 ^ 40 = 1099511627776) by reflexivity.
  rewrite EL, ER, EB, E40.
  set (g := H / 101) in *. set (sc := slot_cap 536866816) in *. lia.
Qed.

Theorem pack_big_fit : forall x, Z.of_nat (length x) <= pf_MAX ->
  CAPOK2 (GALL (CS_of (beta2_x x))) (GMAP (CS_of (beta2_x x))) pq_BMAX pq_NMAX.
Proof.
  intros x Hn. destruct (beta2_x_own x) as (H0 & Hz & Hs).
  assert (Hzk : forall k, 0 <= k < 49 -> pv k = 0 -> beta2_x x k = 0).
  { intros k Hk E. rewrite (po_zero_k k Hk (proj2 (pv_pw k Hk) E)). exact Hz. }
  destruct (pf_bounds (CS_of (beta2_x x)) (beta2_x x) (Z.of_nat (length x)) ltac:(lia)
              (CS_of_bound (beta2_x x) (fun k _ => H0 k)) Hs Hzk) as (G0 & G1 & G2).
  apply pb_capok; assumption.
Qed.

Lemma room_pack_big : forall b r,
  CAPOK2 (GALL (pb_cap b)) (GMAP (pb_cap b)) pq_BMAX pq_NMAX ->
  0 <= r <= pq_NMAX -> pb_bytes b + r <= pq_BMAX ->
  znth (band r) (pb_live b) + 1 <= znth (band r) (pb_cap b) -> room_pack b r.
Proof. intros b r C Hr Hb Hl. exact (room_pack_of b r pq_BMAX pq_NMAX C Hr Hb Hl). Qed.
