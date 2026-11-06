(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0l.v, with its module paths changed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Lemma chunk_offs_weight : forall U pp cc bb s c, WfP U pp cc bb s -> 1 <= c <= 31 ->
class_size c * Z.of_nat (length (chunk_offs s c)) <= crw (st_chunks s).
Proof.
intros U pp cc bb s c W Hc. pose proof (class_ok c Hc) as (Ksz & _).
pose proof (wf_chunks _ _ _ _ _ W) as CK. unfold chunk_offs. induction CK as [|k t Hk Ht IH]; [cbn; lia|].
cbn [flat_map]. rewrite length_app, Nat2Z.inj_add. change (crw (k :: t)) with (cw k + crw t). pose proof (cw_nonneg k) as N.
destruct Hk as [_ Hk]. unfold cw. destruct (ck_beg k) as [|off|r o|cid pos]; cbn [length]; try lia.
destruct Hk as (_ & Hcls & _). destruct (Z.eqb_spec (prim_class off) c) as [Ec|Ne]; cbn [length]; [|lia].
rewrite <- Hcls, Ec. lia.
Qed.
Lemma class_size_batch : class_size kBatchClass = kBatchBytes. Proof. reflexivity. Qed.
Lemma nrecZ_rbytes : forall U pp cc bb s c, WfP U pp cc bb s -> 1 <= c <= 31 -> class_size c * nrecZ s c <= rbytes s.
Proof.
intros U pp cc bb s c W Hc. pose proof (chunk_offs_weight U pp cc bb s c W Hc) as CW. pose proof (class_ok c Hc) as (Ksz & _).
unfold nrecZ, rbytes. rewrite Nat2Z.inj_add. unfold batch_offs. destruct (Z.eqb_spec c kBatchClass) as [->|Ne].
- rewrite length_map, class_size_batch in *. lia.
- cbn [length]. unfold kBatchBytes. lia.
Qed.
Lemma nrecZ_count : forall s c, nrecZ s c <= Z.of_nat (length (st_chunks s)) + Z.of_nat (length (all_batches s)).
Proof. intros s c. pose proof (length_chunk_offs_le s c). pose proof (length_batch_offs_le s c). unfold nrecZ. lia. Qed.
Lemma sec_arr_le_secs : forall U pp cc bb s, WfP U pp cc bb s -> (length (st_sec_arr s) <= length (st_secs s))%nat.
Proof.
intros U pp cc bb s W. pose proof (wf_secondary _ _ _ _ _ W) as X. destruct X as [Snd _ Sal _ _].
rewrite <- (length_seq (length (st_secs s)) 0%nat). apply NoDup_incl_length; [exact Snd|].
intros r Hr. apply Sal in Hr as (sm & E & _). apply in_seq. split; [lia|]. cbn. eapply nth_error_lt. exact E.
Qed.
Theorem regime_big_intro : forall U s, Wf U s -> BigInv s ->
rbytes s + 8 * kMaxSize + 2 ^ 20 <= kUserMapSize * EV_MAX ->
Z.of_nat (length (st_chunks s)) + Z.of_nat (length (all_batches s)) + 10248 <= 65536 ->
Z.of_nat (length (st_secs s)) < kPtrArrayEntriesPerCommit ->
qc_bytes (st_qglobal s) + qc_bytes (st_qthread s) + 2 ^ 29 <= 2 ^ 36 ->
regime_big s.
Proof.
intros U s W BI HB HC HS HQ. unfold regime_big. split; [exact BI|]. split; [|split; [|split]].
- intros c Hc. pose proof (nrecZ_rbytes U 0 0 0 s c W Hc) as NB. pose proof (nrecZ_count s c) as NC.
pose proof (class_ok c Hc) as (Ksz & _ & Kmax & _). split; [|lia].
assert (class_size c * (nrecZ s c + 8) = class_size c * nrecZ s c + 8 * class_size c) as -> by lia. lia.
- pose proof (sec_arr_le_secs U 0 0 0 s W). lia.
- lia.
- exact HQ.
Qed.
Definition class_weight_okb (n : Z) : bool := negb (from_primary n) || (class_size (chunk_class n) <=? 2 * n + 96).
Lemma class_weight_bound : forall n, 0 <= n -> from_primary n = true -> class_size (chunk_class n) <= 2 * n + 96.
Proof.
assert (H : zall (Z.to_nat (65536 - 0 + 1)) 0 class_weight_okb = true) by (vm_compute; reflexivity).
intros n Hn Hp.
assert (Hle : n <= 65536).
{ pose proof (needed_primary_bounds n Hn) as (N1 & _). pose proof (req_size_bounds n Hn) as (_ & _ & Q & _). pose proof (rz_size_bounds n) as [R _].
unfold from_primary in Hp. apply Z.leb_le in Hp. unfold kMaxSize in Hp. lia. }
pose proof (zall_range 0 65536 _ H n ltac:(lia)) as Hb. unfold class_weight_okb in Hb. rewrite Hp in Hb. cbn [negb orb] in Hb. apply Z.leb_le. exact Hb.
Qed.
Lemma rbytes_mgrow : forall s n s', mgrow s n s' ->
rbytes s' <= rbytes s + (if from_primary n then class_size (chunk_class n) else 0) /\
length (all_batches s') = length (all_batches s) /\
qc_bytes (st_qglobal s') + qc_bytes (st_qthread s') = qc_bytes (st_qglobal s) + qc_bytes (st_qthread s).
Proof.
intros s n s' (_ & C & _ & Q1 & Q2 & _). unfold rbytes, all_batches. rewrite Q1, Q2. split; [lia | split; reflexivity].
Qed.
Lemma rbytes_fgrow : forall s s', fgrow s s' -> rbytes s' <= rbytes s + kBatchBytes.
Proof. intros s s' (_ & C & _ & B). unfold rbytes, kBatchBytes in *. lia. Qed.
Lemma regime_big_malloc : forall s n s', 0 <= n -> mgrow s n s' ->
Z.of_nat (length (st_chunks s')) + Z.of_nat (length (all_batches s')) <= Z.of_nat (length (st_chunks s)) + Z.of_nat (length (all_batches s)) + 1 /\
rbytes s' <= rbytes s + 2 * n + 96 /\
Z.of_nat (length (st_secs s')) <= Z.of_nat (length (st_secs s)) + 1.
Proof.
intros s n s' Hn G. destruct (rbytes_mgrow s n s' G) as (RB & AB & _). destruct G as (K & _ & S & _). rewrite AB.
split; [lia|]. split.
- destruct (from_primary n) eqn:Hp; [pose proof (class_weight_bound n Hn Hp) | ]; lia.
- destruct (from_primary n); lia.
Qed.
Lemma regime_big_free : forall s s', fgrow s s' ->
Z.of_nat (length (st_chunks s')) + Z.of_nat (length (all_batches s')) <= Z.of_nat (length (st_chunks s)) + Z.of_nat (length (all_batches s)) + 1 /\
rbytes s' <= rbytes s + kBatchBytes /\
length (st_secs s') = length (st_secs s).
Proof.
intros s s' G. pose proof (rbytes_fgrow s s' G) as RB. destruct G as (K & _ & S & B). split; [lia | split; [exact RB | exact S]].
Qed.
Lemma qtight_queue_bytes : forall s, qtight s -> qc_bytes (st_qglobal s) + qc_bytes (st_qthread s) + 2 ^ 29 <= 2 ^ 36.
Proof. intros s (A & B & _). unfold kQuarantineCacheMax, kQuarantineMax in *. lia. Qed.
Lemma free_cached_le_carved : forall U pp cc bb s c, WfP U pp cc bb s -> 1 <= c <= 31 ->
class_size c * (fa_len (rg_free (reg s c)) + Z.of_nat (length (pc_chunks (cache s c)))) <= rg_alloc_user (reg s c).
Proof.
intros U pp cc bb s c W Hc. pose proof (class_ok c Hc) as (Ksz & _).
pose proof (wf_classes _ _ _ _ _ W c Hc) as C. unfold wf_class in C.
pose proof (wr_nodup _ _ _ _ _ _ C) as ND. pose proof (wr_elems _ _ _ _ _ _ C) as EL. pose proof (wr_runs _ _ _ _ _ _ C) as R.
pose proof (wr_alloc _ _ _ _ _ _ C) as A. pose proof (wr_alloc_al _ _ _ _ _ _ C) as AL.
rewrite app_assoc in ND, EL. apply NoDup_app_iff in ND as (ND & _ & _). apply Forall_app in EL as [EL _].
pose proof (multiples_bound (class_size c) (rg_alloc_user (reg s c)) _ Ksz ltac:(lia) AL ND EL) as MB.
rewrite length_app, Nat2Z.inj_add in MB. rewrite <- (fa_elems_length (class_size c)) by exact R. exact MB.
Qed.
Theorem return_room_big : forall U pp cc bb s c, WfP U pp cc bb s -> 1 <= c <= 31 -> BigP s ->
4 * (fa_len (rg_free (reg s c)) + Z.of_nat (length (pc_chunks (cache s c)))) <= rg_mapped_fa (reg s c).
Proof.
intros U pp cc bb s c W Hc HB. pose proof (free_cached_le_carved U pp cc bb s c W Hc) as FC. pose proof (class_ok c Hc) as (Ksz & _).
pose proof (wf_classes _ _ _ _ _ W c Hc) as C. unfold wf_class in C. pose proof (wr_fa _ _ _ _ _ _ C) as [F0 _].
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ C)) as N0.
destruct (HB c Hc) as [Z0|HR].
- rewrite Z0 in FC. assert (fa_len (rg_free (reg s c)) + Z.of_nat (length (pc_chunks (cache s c))) <= 0) by nia. lia.
- assert (fa_len (rg_free (reg s c)) + Z.of_nat (length (pc_chunks (cache s c))) <= rg_alloc_user (reg s c) / class_size c).
{ apply Z.div_le_lower_bound; [lia|]. lia. }
lia.
Qed.
Lemma all_batches_bound : forall U pp cc bb s, WfP U pp cc bb s -> qc_bytes (st_qglobal s) <= kQuarantineMax ->
kBatchSlots * (Z.of_nat (length (all_batches s)) - 258) <= Z.of_nat (length (st_chunks s)).
Proof.
intros U pp cc bb s W HG. pose proof (wf_quarantine _ _ _ _ _ W) as Q.
destruct (qbatches_bound U pp cc bb s W) as (ng & NG0 & C1 & C2).
pose proof (almost_full_items _ (wq_tfull _ Q)) as T1. pose proof (q_items_le_chunks U pp cc bb s W) as QL.
unfold q_items, all_batches in *. rewrite flat_map_app, !length_app in *. rewrite !Nat2Z.inj_add.
unfold kBatchSlots, kQuarantineCacheMax, kQuarantineMax in *. lia.
Qed.
Lemma from_primary_small : forall n, 0 <= n <= 63472 -> from_primary n = true.
Proof.
intros n Hn. unfold from_primary. apply Z.leb_le. pose proof (needed_primary_bounds n ltac:(lia)) as (_ & (_ & N) & _). unfold kMaxSize. lia.
Qed.
Theorem regime_big_intro2 : forall U s, Wf U s -> BigInv s -> qtight s ->
Z.of_nat (length (st_chunks s)) <= 54000 ->
crw (st_chunks s) + 2 ^ 23 <= kUserMapSize * EV_MAX ->
Z.of_nat (length (st_secs s)) < kPtrArrayEntriesPerCommit ->
regime_big s.
Proof.
intros U s W BI QT HC HW HS. pose proof QT as (_ & QG & _). pose proof (all_batches_bound U 0 0 0 s W QG) as AB.
apply (regime_big_intro U s W BI); [ | | exact HS | exact (qtight_queue_bytes s QT)].
- unfold rbytes, kBatchBytes, kBatchSlots, kMaxSize, kUserMapSize, EV_MAX in *. lia.
- unfold kBatchSlots in *. lia.
Qed.
Lemma budget_malloc : forall s n s', 0 <= n -> mgrow s n s' ->
Z.of_nat (length (st_chunks s')) <= Z.of_nat (length (st_chunks s)) + 1 /\
crw (st_chunks s') <= crw (st_chunks s) + 2 * n + 96 /\
Z.of_nat (length (st_secs s')) <= Z.of_nat (length (st_secs s)) + (if n <=? 63472 then 0 else 1).
Proof.
intros s n s' Hn (K & C & S & _). split; [exact K|]. split.
- destruct (from_primary n) eqn:Hp; [pose proof (class_weight_bound n Hn Hp) | ]; lia.
- destruct (Z.leb_spec n 63472) as [Hle|Hgt]; [rewrite (from_primary_small n ltac:(lia)) in S; exact S | destruct (from_primary n); lia].
Qed.
Lemma budget_free : forall s s', fgrow s s' ->
Z.of_nat (length (st_chunks s')) <= Z.of_nat (length (st_chunks s)) /\ crw (st_chunks s') <= crw (st_chunks s) /\
length (st_secs s') = length (st_secs s).
Proof. intros s s' (K & C & S & _). auto. Qed.
Theorem return_room : forall U pp cc bb s c, WfP U pp cc bb s -> 1 <= c <= 31 ->
4 * (Z.of_nat (length (class_elems s c)) + 1 + (cc + bslack c bb + 2 * (EV_MAX - st_nev s))) <= rg_mapped_fa (reg s c) ->
4 * (fa_len (rg_free (reg s c)) + Z.of_nat (length (pc_chunks (cache s c)))) <= rg_mapped_fa (reg s c).
Proof.
intros U pp cc bb s c W Hc HROOM. destruct (wf_regime _ _ _ _ _ W) as [Hs|[HP _]]; [|exact (return_room_big U pp cc bb s c W Hc HP)].
pose proof (wf_slack _ _ _ _ _ W) as (_ & C0 & B0). pose proof (bslack_le c bb B0) as BS.
pose proof (wf_classes _ _ _ _ _ W c Hc) as C. unfold wf_class in C. pose proof (fa_elems_length (class_size c) _ (wr_runs _ _ _ _ _ _ C)) as FL.
unfold class_elems in HROOM. rewrite !length_app, !Nat2Z.inj_add, FL in HROOM. lia.
Qed.
Theorem batches_len_bound : forall U pp cc bb s, WfP U pp cc bb s ->
qc_bytes (st_qglobal s) + qc_bytes (st_qthread s) <= 2 ^ 36 -> 0 <= qc_bytes (st_qthread s) ->
Z.of_nat (length (all_batches s)) <= 2 ^ 17.
Proof.
intros U pp cc bb s W HQ HT. destruct (wf_regime _ _ _ _ _ W) as [Hs|[_ HC]].
- pose proof (batches_bound U pp cc bb s W Hs). unfold EV_MAX in *. lia.
- pose proof (wf_slack _ _ _ _ _ W) as (_ & C0 & _). pose proof (wf_quarantine _ _ _ _ _ W) as Q.
destruct (qbatches_bound U pp cc bb s W) as (ng & NG0 & C1 & C2).
pose proof (almost_full_items _ (wq_tfull _ Q)) as T1. pose proof (q_items_le_chunks U pp cc bb s W) as QL.
unfold q_items, all_batches in *. rewrite flat_map_app, !length_app in *. rewrite !Nat2Z.inj_add.
unfold kBatchSlots, kQuarantineCacheMax in *. lia.
Qed.
Definition nrec (s : astate) : Z := Z.of_nat (length (st_chunks s)).
Definition wpot (s : astate) : Z := crw (st_chunks s) + 2 ^ 17 * Z.of_nat (length (st_secs s)).
Definition NREC_MAX : Z := 54000.
Definition WPOT_MAX : Z := 2 ^ 31 - 2 ^ 23.
Definition wcost (n : Z) : Z := if n <=? 63472 then 2 * n + 96 else 2 ^ 17.
Definition hcost (n : Z) : Z := if n <=? 63472 then 0 else n / 8 + 10242.
Definition HULL_UNIT : Z := 2 ^ 25 + 2 ^ 14.
Definition bud_ok (s : astate) (e c w h : Z) : Prop :=
st_nev s + e <= EV_BIG /\ nrec s + c <= NREC_MAX /\ wpot s + w <= WPOT_MAX /\ sec_hulls s + h <= HPOT_MAX.
Definition bud_le (s s' : astate) (e c w h : Z) : Prop :=
st_nev s' <= st_nev s + e /\ nrec s' <= nrec s + c /\ wpot s' <= wpot s + w /\ sec_hulls s' <= sec_hulls s + h.
Lemma wcost_range : forall n, 0 <= n -> 0 <= wcost n <= 2 ^ 17.
Proof. intros n Hn. unfold wcost. destruct (Z.leb_spec n 63472); lia. Qed.
Lemma hcost_range : forall n, 0 <= n < MALLOC_MAX -> 0 <= hcost n <= HULL_UNIT.
Proof.
intros n Hn. unfold hcost, HULL_UNIT, MALLOC_MAX in *. destruct (Z.leb_spec n 63472); [lia|].
pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)). assert (n / 8 <= 2 ^ 28 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 28 / 8) with (2 ^ 25) in *. lia.
Qed.
Lemma bud_le_refl : forall s, bud_le s s 0 0 0 0. Proof. intros s. unfold bud_le. lia. Qed.
Lemma bud_le_trans : forall s1 s2 s3 e c w h e' c' w' h',
bud_le s1 s2 e c w h -> bud_le s2 s3 e' c' w' h' -> bud_le s1 s3 (e + e') (c + c') (w + w') (h + h').
Proof. intros s1 s2 s3 e c w h e' c' w' h' (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold bud_le. lia. Qed.
Lemma bud_le_mono : forall s s' e c w h e' c' w' h', bud_le s s' e c w h -> e <= e' -> c <= c' -> w <= w' -> h <= h' -> bud_le s s' e' c' w' h'.
Proof. intros s s' e c w h e' c' w' h' (A1 & A2 & A3 & A4) He Hc Hw Hh. unfold bud_le. lia. Qed.
Lemma bud_ok_le : forall s s' e c w h e' c' w' h',
bud_ok s (e + e') (c + c') (w + w') (h + h') -> bud_le s s' e c w h -> bud_ok s' e' c' w' h'.
Proof. intros s s' e c w h e' c' w' h' (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold bud_ok. lia. Qed.
Lemma bud_ok_mono : forall s e c w h e' c' w' h', bud_ok s e c w h -> e' <= e -> c' <= c -> w' <= w -> h' <= h -> bud_ok s e' c' w' h'.
Proof. intros s e c w h e' c' w' h' (A1 & A2 & A3 & A4) He Hc Hw Hh. unfold bud_ok. lia. Qed.
Lemma bud_le_set_fs : forall f s, bud_le s (set_fs f s) 0 0 0 0. Proof. intros f s. unfold bud_le, nrec, wpot, sec_hulls. cbn [st_nev st_chunks st_secs set_fs]. lia. Qed.
Lemma bud_ok_set_fs : forall f s e c w h, bud_ok (set_fs f s) e c w h <-> bud_ok s e c w h. Proof. intros f s e c w h. split; intros H; exact H. Qed.
Lemma sec_hull_le_hcost : forall n, 0 <= n -> from_primary n = false -> sec_map_size n / 8 + 8192 <= hcost n.
Proof.
intros n Hn Hp. unfold hcost. destruct (Z.leb_spec n 63472) as [Hle|Hgt]; [rewrite (from_primary_small n ltac:(lia)) in Hp; discriminate|].
assert (SB : sec_map_size n <= n + 1 + 2 ^ 14).
{ unfold sec_map_size, needed_size. rewrite Hp.
pose proof (needed_primary_bounds n Hn) as (N1 & N2 & N3). pose proof (rz_size_bounds n) as [R1 R2].
assert (RU : forall x, 0 <= x -> round_up x kPage < x + kPage).
{ intros x Hx. unfold round_up, kPage. pose proof (Z.mul_div_le (x + 4096 - 1) 4096 ltac:(lia)). lia. }
pose proof (RU (needed_primary n + rz_size n) ltac:(lia)). unfold kPage in *. lia. }
assert (sec_map_size n / 8 <= (n + 1 + 2 ^ 14) / 8) by (apply Z.div_le_mono; lia).
assert ((n + 1 + 2 ^ 14) / 8 <= n / 8 + 2049).
{ replace (n + 1 + 2 ^ 14) with (n + 1 + 2048 * 8) by lia. rewrite Z.div_add by lia.
pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.div_mod (n + 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 1) 8 ltac:(lia)). lia. }
lia.
Qed.
Theorem bud_malloc : forall s n s', 0 <= n -> mgrow s n s' -> st_nev s' = st_nev s + 1 -> bud_le s s' 1 1 (wcost n) (hcost n).
Proof.
intros s n s' Hn (K & C & S & _ & _ & H) NE. unfold bud_le, nrec, wpot, hgrow in *. split; [lia|]. split; [exact K|].
pose proof (hcost_range n) as HR. unfold wcost, hcost in *.
destruct (from_primary n) eqn:Hp.
- pose proof (class_weight_bound n Hn Hp) as CW. pose proof (primary_geometry n Hn Hp) as (_ & _ & KM & _ & K0). unfold kMaxSize in KM.
destruct (Z.leb_spec n 63472); split; try lia. pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)). lia.
- pose proof (sec_hull_le_hcost n Hn Hp) as SH. unfold hcost in SH.
destruct (Z.leb_spec n 63472) as [Hle|Hgt]; [rewrite (from_primary_small n ltac:(lia)) in Hp; discriminate|]. split; lia.
Qed.
Lemma sec_hulls_ext : forall s s', secs_ext s s' -> length (st_secs s') = length (st_secs s) -> sec_hulls s' = sec_hulls s.
Proof.
intros s s' X L. unfold sec_hulls, secs_ext in *. revert X L. generalize (st_secs s') as l'. generalize (st_secs s) as l.
induction l as [|a t IH]; intros l' X L; destruct l' as [|a' t']; try discriminate; [reflexivity|]. cbn [fold_right].
destruct (X 0%nat a eq_refl) as (sm' & E & EL & _). cbn in E. injection E as <-.
rewrite EL. f_equal. apply IH; [intros r sm Hr; exact (X (S r) sm Hr) | cbn in L; lia].
Qed.
Theorem bud_free : forall U s p n ns r, fgrow s (snd r) -> free_post U s p n ns r -> bud_le s (snd r) 1 0 0 0.
Proof.
intros U s p n ns r (K & C & S & _) (_ & NE & SX & _). unfold bud_le, nrec, wpot. rewrite (sec_hulls_ext s (snd r) SX S), S. lia.
Qed.
Lemma crw_nonneg : forall l, 0 <= crw l.
Proof. induction l as [|k t IH]; [cbn; lia|]. change (crw (k :: t)) with (cw k + crw t). pose proof (cw_nonneg k). lia. Qed.
Theorem aregime_intro : forall U s, Wf U s -> BigInv s -> qtight s -> bud_ok s 1 0 0 0 -> aregime s.
Proof.
intros U s W BI QT (E & C & Wt & H). right. unfold nrec, wpot, NREC_MAX, WPOT_MAX in *.
pose proof (crw_nonneg (st_chunks s)) as C0.
split; [|split; [unfold EV_BIG in *; lia | lia]].
apply (regime_big_intro2 U s W BI QT); unfold kUserMapSize, EV_MAX, kPtrArrayEntriesPerCommit; lia.
Qed.
Definition VEV_MAX : Z := 6000.
Definition cdivZ (a b : Z) : Z := (a + b - 1) / b.
Definition vev (s : astate) : Z :=
Z.max (st_nev s - (EV_BIG - VEV_MAX))
(Z.max (nrec s - (NREC_MAX - VEV_MAX))
(Z.max (cdivZ (wpot s) (2 ^ 17) - (WPOT_MAX / 2 ^ 17 - VEV_MAX))
(cdivZ (sec_hulls s) HULL_UNIT - (HPOT_MAX / HULL_UNIT - VEV_MAX)))).
Lemma cdivZ_le : forall a b q, 0 < b -> cdivZ a b <= q -> a <= b * q.
Proof. intros a b q Hb H. unfold cdivZ in H. pose proof (Z.div_mod (a + b - 1) b ltac:(lia)). pose proof (Z.mod_pos_bound (a + b - 1) b Hb). nia. Qed.
Lemma cdivZ_step : forall a a' b k, 0 < b -> a' <= a + b * k -> cdivZ a' b <= cdivZ a b + k.
Proof.
intros a a' b k Hb H. unfold cdivZ. replace (a + b * k + b - 1) with (a + b - 1 + k * b) in * by lia.
rewrite <- (Z.div_add (a + b - 1) k b) by lia. apply Z.div_le_mono; lia.
Qed.
Theorem vev_bud : forall s e, vev s + e <= VEV_MAX -> bud_ok s e e (2 ^ 17 * e) (HULL_UNIT * e).
Proof.
intros s e H. unfold vev in H.
assert (H1 : st_nev s - (EV_BIG - VEV_MAX) + e <= VEV_MAX) by lia.
assert (H2 : nrec s - (NREC_MAX - VEV_MAX) + e <= VEV_MAX) by lia.
assert (H3 : cdivZ (wpot s) (2 ^ 17) <= WPOT_MAX / 2 ^ 17 - e) by lia.
assert (H4 : cdivZ (sec_hulls s) HULL_UNIT <= HPOT_MAX / HULL_UNIT - e) by lia.
apply cdivZ_le in H3; [|lia]. apply cdivZ_le in H4; [|unfold HULL_UNIT; lia].
unfold bud_ok. unfold WPOT_MAX, HPOT_MAX, HULL_UNIT, VEV_MAX, EV_BIG, NREC_MAX in *.
change ((2 ^ 31 - 2 ^ 23) / 2 ^ 17) with 16320 in H3. change (3 * 2 ^ 36 / (2 ^ 25 + 2 ^ 14)) with 6141 in H4. lia.
Qed.
Theorem vev_le : forall s s' k, 0 <= k -> bud_le s s' k k (2 ^ 17 * k) (HULL_UNIT * k) -> vev s' <= vev s + k.
Proof.
intros s s' k Hk (A1 & A2 & A3 & A4). unfold vev.
pose proof (cdivZ_step (wpot s) (wpot s') (2 ^ 17) k ltac:(lia) A3) as B3.
pose proof (cdivZ_step (sec_hulls s) (sec_hulls s') HULL_UNIT k ltac:(unfold HULL_UNIT; lia) A4) as B4. lia.
Qed.
Corollary aregime_vev : forall U s, Wf U s -> BigInv s -> qtight s -> vev s < VEV_MAX -> aregime s.
Proof.
intros U s W BI QT H. apply (aregime_intro U s W BI QT). pose proof (vev_bud s 1 ltac:(lia)) as B.
eapply bud_ok_mono; [exact B | lia | lia | lia | unfold HULL_UNIT; lia].
Qed.
