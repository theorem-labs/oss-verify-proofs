From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjSame pj_get_c.
Import ListNotations.
Open Scope Z_scope.

Lemma entd_cb : forall m k s, mem_inv rsegs m -> 0 <= k -> k + Z.of_nat (length s) + 1 <= 2 ^ 64 ->
  forallb (fun c => (0 <? c) && (c <? 256)) s = true ->
  ro_bytes_b rsegs k (map (Z_to_bv 8) (s ++ [0])) = true -> pj_cbytes rsegs m k s.
Proof.
  intros m k s MI H0 H1 HF HB. split.
  - apply Forall_forall. intros c Hc. rewrite forallb_forall in HF. specialize (HF c Hc).
    apply andb_prop in HF as [A B]. apply Z.ltb_lt in A. apply Z.ltb_lt in B. lia.
  - apply ro_bytes_at; [exact MI | exact H0 | rewrite length_map, length_app; cbn [length]; lia |].
    apply ro_bytes_b_sound. exact HB.
Qed.

Lemma entd_apart : forall a n lo hi, 0 < n -> lo < hi -> (forall x, a <= x < a + n -> ~ (lo <= x < hi)) ->
  a + n <= lo \/ hi <= a.
Proof.
  intros a n lo hi Hn Hl H. destruct (Z_le_dec (a + n) lo) as [E|E]; [left; exact E|].
  destruct (Z_le_dec hi a) as [E'|E']; [right; exact E'|].
  exfalso. apply (H (Z.max a lo)); lia.
Qed.

Lemma entd_roc8 : forall m A v, pj_u64 rsegs m A v -> ro_cells rsegs m A [C8 (Z_to_bv 64 v)].
Proof. intros m A v (_ & HB). split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]. Qed.

Lemma entd_roc4 : forall m A v, pj_u32 rsegs m A v -> ro_cells rsegs m A [C4 (Z_to_bv 64 v)].
Proof. intros m A v (_ & HB). split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]. Qed.

Lemma entd_rng : forall m L o u Du, pj_node rsegs m L o u Du -> 0 <= o /\ o + 56 <= 2 ^ 64.
Proof.
  intros m L o u Du H. destruct (pj_view rsegs m L o u Du H) as (num & str & kids & keys & n & cap & Hh & _).
  destruct Hh as ((_ & H0 & H1 & _) & _). lia.
Qed.

Lemma entd_hit_foot : forall m L o members D i kname v kids x,
  pj_node rsegs m L o (JObj members) D -> nth_error members i = Some (kname, v) -> pj_u64 rsegs m (o + 24) kids ->
  kids + 56 * Z.of_nat i <= x < kids + 56 * Z.of_nat i + 56 -> pj_foot o D x.
Proof.
  intros m L o members D i kname v kids x HN Ei Hk Hx.
  assert (Es : nth_error (slots (JObj members)) i = Some (Some kname, v))
    by (cbn [slots]; rewrite nth_error_map, Ei; reflexivity).
  destruct (pj_slot rsegs m L o (JObj members) D i (Some kname) v HN Es)
    as (num & str & kids' & keys & n & cap & D1 & Hh & _ & _ & _ & HF1 & _).
  pose proof Hh as (_ & _ & _ & _ & Hk' & _).
  rewrite (pj_u64_uniq rsegs m (o + 24) kids' kids Hk' Hk) in HF1.
  apply HF1. left. exact Hx.
Qed.

Lemma entd_get_sub : forall m L o t D kname z, pj_node rsegs m L o t D -> pj_get_res m L o t D kname z ->
  z = 0 \/ exists v Dz, pj_node rsegs m L z v Dz /\ (forall x, pj_foot z Dz x -> pj_foot o D x).
Proof.
  intros m L o t D kname z HN HR.
  destruct t as [| | | txt bits | s | items | members]; cbn [pj_get_res] in HR; try (left; exact HR).
  destruct HR as [(_ & Hz)|(i & v & kids & Di & Ei & _ & Hk & Ez & Hv & Hinc)]; [left; exact Hz|]. right.
  exists v, Di. split; [subst z; exact Hv|].
  intros x [Hx|(b & Hb & Hx)].
  - subst z. exact (entd_hit_foot m L o members D i kname v kids x HN Ei Hk Hx).
  - right. exists b. split; [apply Hinc; exact Hb | exact Hx].
Qed.

Lemma entd_node_tr : forall W m m' L p u Du, pj_node rsegs m L p u Du -> munch W m m' ->
  (forall x, pj_foot p Du x -> outside W x) -> pj_node rsegs m' L p u Du.
Proof.
  intros W m m' L p u Du H MU HO.
  exact (pj_node_munch rsegs W m L m' L p u Du H (pj_node_blocks rsegs u m L p Du H) MU HO).
Qed.

Lemma entd_res_tr : forall W m m' L o t D kname z, pj_node rsegs m L o t D -> pj_get_res m L o t D kname z ->
  munch W m m' -> (forall x, pj_foot o D x -> outside W x) -> pj_get_res m' L o t D kname z.
Proof.
  intros W m m' L o t D kname z HN HR MU HO.
  destruct t as [| | | txt bits | s | items | members]; cbn [pj_get_res] in HR |- *; try exact HR.
  destruct HR as [HR|(i & v & kids & Di & Ei & Hf & Hk & Ez & Hv & Hinc)]; [left; exact HR|right].
  exists i, v, kids, Di. split; [exact Ei|]. split; [exact Hf|].
  split; [apply (pj_u64_eq rsegs m m'); [exact Hk | intros x Hx; apply MU; apply HO; left; lia]|].
  split; [exact Ez|]. split; [|exact Hinc].
  apply (entd_node_tr W m m' L z v Di Hv MU).
  intros x [Hx|(b & Hb & Hx)]; apply HO.
  - subst z. exact (entd_hit_foot m L o members D i kname v kids x HN Ei Hk Hx).
  - right. exists b. split; [apply Hinc; exact Hb | exact Hx].
Qed.

Lemma entd_arr : forall m L p items Du i u, pj_node rsegs m L p (JArr items) Du -> nth_error items i = Some u ->
  exists kids cap D1, pj_u64 rsegs m (p + 24) kids /\ Z.of_nat i < cap /\ L kids (56 * cap) /\
    pj_node rsegs m L (kids + 56 * Z.of_nat i) u D1 /\
    (forall x, pj_foot (kids + 56 * Z.of_nat i) D1 x -> pj_foot p Du x).
Proof.
  intros m L p items Du i u HN Ei.
  assert (Es : nth_error (slots (JArr items)) i = Some (None, u))
    by (cbn [slots]; rewrite nth_error_map, Ei; reflexivity).
  destruct (pj_slot rsegs m L p (JArr items) Du i None u HN Es)
    as (num & str & kids & keys & n & cap & D1 & Hh & Hic & HLk & HP1 & HF1 & _).
  pose proof Hh as (_ & _ & _ & _ & Hk & _).
  exists kids, cap, D1. auto.
Qed.

Lemma entd_arr_hdr : forall m L p items Du, pj_node rsegs m L p (JArr items) Du ->
  pj_u32 rsegs m p 5 /\ pj_u64 rsegs m (p + 40) (Z.of_nat (length items)) /\
  exists kids cap, pj_u64 rsegs m (p + 24) kids /\ Z.of_nat (length items) <= cap /\
    (cap = 0 \/ L kids (56 * cap)).
Proof.
  intros m L p items Du HN. cbn [pj_node] in HN.
  destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & _).
  pose proof Hh as (_ & Ht & _ & _ & Hk & _ & Hn & _). subst n.
  split; [exact Ht|]. split; [exact Hn|]. exists kids, cap. split; [exact Hk|]. split; [lia|].
  destruct Hcap as [(C0 & _)|(_ & HL)]; [left; exact C0 | right; exact HL].
Qed.

Lemma entd_tag5 : forall m L p u Du, pj_node rsegs m L p u Du -> tag u = 5 -> exists items, u = JArr items.
Proof. intros m L p u Du _ H. destruct u; cbn in H; try lia. eexists; reflexivity. Qed.

Lemma entd_ty : forall m L p u Du, pj_node rsegs m L p u Du -> pj_u32 rsegs m p (tag u).
Proof.
  intros m L p u Du H. destruct (pj_view rsegs m L p u Du H) as (num & str & kids & keys & n & cap & Hh & _).
  exact (proj1 (proj2 Hh)).
Qed.
