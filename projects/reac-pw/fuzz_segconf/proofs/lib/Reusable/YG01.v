(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG01.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: wf_depot no longer requires the depot to lie inside U; traces outside U (wild) are charged to st_nev, up to WILD_MAX = EV_MAX (depot_inv, tr_admit, the depot size lemmas and DEPOT_CAP). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Definition reg (s : astate) (c : Z) : region := znth region0 c (st_regions s).
Definition cache (s : astate) (c : Z) : pclass := znth pclass0 c (st_cache s).
Definition areq_ok (s : astate) (q : kreq) : Prop :=
match q with
| KMapUser c off len =>
1 <= c <= 31 /\ off = rg_mapped_user (reg s c) /\ len = kUserMapSize /\
0 <= off /\ off mod kUserMapSize = 0 /\ off + len <= kFreeArrayOffset /\
Forall (fun h => fst h = off /\ snd h = len \/ fst h + snd h <= off \/ off + len <= fst h) (rg_holes (reg s c))
| KMapFreeArray c off len =>
1 <= c <= 31 /\ off = rg_mapped_fa (reg s c) /\ len = kFreeArrayMapSize /\
0 <= off /\ off mod kFreeArrayMapSize = 0 /\ off + len <= kFreeArrayMax /\
Forall (fun h => fst h = kFreeArrayOffset + off /\ snd h = len \/
fst h + snd h <= kFreeArrayOffset + off \/ kFreeArrayOffset + off + len <= fst h) (rg_holes (reg s c))
| KMapPtrArray off len =>
off = 8 * st_sec_reserved s /\ len = kPtrArrayCommit /\ 0 <= off /\ off mod kPtrArrayCommit = 0 /\
off + len <= 8 * kMaxNumChunks
| KMmapSec len => exists n, 0 <= n < MALLOC_MAX /\ from_primary n = false /\ len = sec_map_size n
| KMunmapSec r len =>
In r (st_sec_arr s) /\ exists sm, nth_error (st_secs s) r = Some sm /\ sm_live sm = true /\ len = sm_len sm
| KShadowRemap p len =>
kClearShadowMmapThreshold <= len / 8 /\
exists r off sm, p = PSec r off /\ nth_error (st_secs s) r = Some sm /\ sm_live sm = true /\
0 <= off /\ off + len <= sm_len sm /\ off mod 8 = 0
| KDepot tr => (length tr <= kUnwindMax)%nat
end.
Definition is_spin {A : Type} (t : itree astate A) : bool := match t with ISpin _ => true | _ => false end.
Fixpoint agprog {A : Type} (t : itree astate A) : Prop :=
match t with
| IAsk q snap k =>
(match q with
| KDepot _ => forall z, aok snap q z -> is_spin (k z) = false
| _ => is_spin (k 1) = false
end) /\ forall z, aok snap q z -> agprog (k z)
| _ => True
end.
Definition progz (q : kreq) (z : Z) : bool :=
match q with KDepot _ | KMunmapSec _ _ => true | _ => z =? 1 end.
Fixpoint atok {A : Type} (ns : bool) (t : itree astate A) (Q : bool -> A -> Prop) : Prop :=
match t with
| IRet a => Q ns a
| ISpin _ => ns = false
| IFail _ => False
| IAsk q snap k => areq_ok snap q /\ forall z, aok snap q z -> atok (progz q z) (k z) Q
end.
Lemma atok_mono {A} (t : itree astate A) : forall ns (Q Q' : bool -> A -> Prop),
(forall b a, Q b a -> Q' b a) -> atok ns t Q -> atok ns t Q'.
Proof.
induction t as [a | q snap k IH | pc | f]; cbn; intros ns Q Q' HQ H; auto.
destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply IH with (Q := Q); [exact HQ | apply Hk, Hz].
Qed.
Lemma atok_ibind {A B} (t : itree astate A) : forall ns (k : A -> itree astate B) (Q : bool -> B -> Prop),
atok ns t (fun ns' a => atok ns' (k a) Q) -> atok ns (ibind t k) Q.
Proof.
induction t as [a | q snap c IH | pc | f]; cbn; intros ns k Q H; auto.
destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply IH. apply Hk, Hz.
Qed.
Lemma atok_asafe {A} (t : itree astate A) : forall ns Q, atok ns t Q -> asafe t.
Proof.
induction t as [a | q snap k IH | pc | f]; cbn; intros ns Q H; auto.
destruct H as [_ Hk]. intros z Hz. apply (IH z (progz q z) Q). apply Hk, Hz.
Qed.
Lemma atok_nospin {A} (t : itree astate A) : forall Q, atok true t Q -> is_spin t = false.
Proof. destruct t; cbn; intros Q H; try reflexivity. discriminate. Qed.
Lemma aok_one : forall s q, match q with KDepot _ => True | _ => aok s q 1 end.
Proof. intros s q. destruct q; cbn; auto. Qed.
Lemma atok_agprog {A} (t : itree astate A) : forall ns Q, atok ns t Q -> agprog t.
Proof.
induction t as [a | q snap k IH | pc | f]; cbn; intros ns Q H; auto.
destruct H as [_ Hk]. split.
- pose proof (aok_one snap q) as H1. destruct q; try (apply (atok_nospin _ Q); specialize (Hk 1 H1); cbn in Hk; exact Hk).
intros z Hz. apply (atok_nospin _ Q). exact (Hk z Hz).
- intros z Hz. apply (IH z (progz q z) Q). apply Hk, Hz.
Qed.
Lemma atok_apath {A} (t : itree astate A) : forall ns Q tr a, atok ns t Q -> apath t tr a -> exists ns', Q ns' a.
Proof.
induction t as [a' | q snap k IH | pc | f]; cbn; intros ns Q tr a H Hy.
- destruct tr; [subst; eauto | destruct Hy].
- destruct tr as [|[q' z] tr']; [destruct Hy|].
destruct Hy as (-> & Hz & Hy). destruct H as [_ Hk]. eapply IH; [apply Hk, Hz | exact Hy].
- destruct tr; destruct Hy.
- destruct tr; destruct Hy.
Qed.
Fixpoint areqs_ok {A : Type} (t : itree astate A) : Prop :=
match t with
| IAsk q snap k => areq_ok snap q /\ forall z, aok snap q z -> areqs_ok (k z)
| _ => True
end.
Lemma atok_areqs_ok {A} (t : itree astate A) : forall ns Q, atok ns t Q -> areqs_ok t.
Proof.
induction t as [a | q snap k IH | pc | f]; cbn; intros ns Q H; auto.
destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply (IH z (progz q z) Q). apply Hk, Hz.
Qed.
Section d.
Context {A B : Type}.
Implicit Types (Q : bool -> A * astate -> Prop) (s : astate) (ns : bool).
Lemma atok_ret ns (a : A) s Q : Q ns (a, s) -> atok ns (ret a s) Q.
Proof. intros H. exact H. Qed.
Lemma atok_bind ns (m : M B) (k : B -> M A) s Q :
atok ns (m s) (fun ns' r => atok ns' (k (fst r) (snd r)) Q) -> atok ns (bind m k s) Q.
Proof.
intros H. unfold bind. apply atok_ibind.
eapply atok_mono; [|exact H]. intros b [x s'] Hb. exact Hb.
Qed.
Lemma atok_fail ns f s Q : False -> atok ns (@fail A f s) Q.
Proof. intros []. Qed.
Lemma atok_spin pc s Q : atok false (@spin A pc s) Q.
Proof. reflexivity. Qed.
Lemma atok_get ns s (Q : bool -> astate * astate -> Prop) : Q ns (s, s) -> atok ns (get s) Q.
Proof. intros H. exact H. Qed.
Lemma atok_put ns s s' (Q : bool -> unit * astate -> Prop) : Q ns (tt, s') -> atok ns (put s' s) Q.
Proof. intros H. exact H. Qed.
Lemma atok_modify ns f s (Q : bool -> unit * astate -> Prop) : Q ns (tt, f s) -> atok ns (modify f s) Q.
Proof. intros H. exact H. Qed.
Lemma atok_askz ns q s (Q : bool -> Z * astate -> Prop) :
areq_ok s q -> (forall z, aok s q z -> Q (progz q z) (z, s)) -> atok ns (askz q s) Q.
Proof. intros Hr H. cbn. split; [exact Hr|]. intros z Hz. apply H, Hz. Qed.
Lemma atok_mcheck ns (b : bool) tag s (Q : bool -> unit * astate -> Prop) :
b = true -> Q ns (tt, s) -> atok ns (mcheck b tag s) Q.
Proof. intros -> H. exact H. Qed.
Lemma atok_if ns (b : bool) (m1 m2 : M A) s Q :
(b = true -> atok ns (m1 s) Q) -> (b = false -> atok ns (m2 s) Q) -> atok ns ((if b then m1 else m2) s) Q.
Proof. intros H1 H2. destruct b; auto. Qed.
End d.
Lemma atok_tick ns s (Q : bool -> unit * astate -> Prop) : Q ns (tt, set_nev (st_nev s + 1) s) -> atok ns (tick s) Q.
Proof. intros H. exact H. Qed.
Lemma atok_get_region ns c s (Q : bool -> region * astate -> Prop) : Q ns (reg s c, s) -> atok ns (get_region c s) Q.
Proof. intros H. exact H. Qed.
Lemma atok_get_pc ns c s (Q : bool -> pclass * astate -> Prop) : Q ns (cache s c, s) -> atok ns (get_pc c s) Q.
Proof. intros H. exact H. Qed.
Definition DEPOT_MAX : Z := 4096.
Definition universe_ok (U : list (list Z)) : Prop :=
Z.of_nat (length U) <= DEPOT_MAX /\ Forall (fun t => (length t <= kUnwindMax)%nat) U /\ NoDup U.
Definition WILD_MAX : Z := EV_MAX.
Definition wild (U d : list (list Z)) : list (list Z) := filter (fun t => negb (mem_trace t U)) d.
Definition depot_inv (U : list (list Z)) (nev : Z) (d : list (list Z)) : Prop :=
NoDup d /\ Forall (fun t => (length t <= kUnwindMax)%nat) d /\ Z.of_nat (length (wild U d)) <= Z.min nev WILD_MAX.
Definition tr_admit (U : list (list Z)) (s : astate) (tr : list Z) : Prop :=
In tr U \/ ((length tr <= kUnwindMax)%nat /\ st_nev s < EV_MAX).
Definition DEPOT_CAP : Z := 20480.
Lemma depot_cap_ok : DEPOT_MAX + WILD_MAX <= DEPOT_CAP.
Proof. apply Z.leb_le. reflexivity. Qed.
Lemma trace_eqb_true : forall a b, trace_eqb a b = true -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b]; cbn; try discriminate; [reflexivity|].
rewrite Bool.andb_true_iff, Z.eqb_eq. intros [-> H]. rewrite (IH b H). reflexivity.
Qed.
Lemma mem_trace_In : forall t l, mem_trace t l = true -> In t l.
Proof.
intros t l. induction l as [|u l IH]; cbn; [discriminate|]. rewrite Bool.orb_true_iff.
intros [H|H]; [left; symmetry; exact (trace_eqb_true _ _ H) | right; exact (IH H)].
Qed.
Lemma depot_len_split : forall U d, NoDup d -> universe_ok U ->
Z.of_nat (length d) <= DEPOT_MAX + Z.of_nat (length (wild U d)).
Proof.
intros U d ND (HU & _ & _).
assert (E : forall l : list (list Z), length l = (length (filter (fun t => mem_trace t U) l) + length (filter (fun t => negb (mem_trace t U)) l))%nat).
{ intros l. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (mem_trace x U); cbn; lia. }
assert (K : (length (filter (fun t => mem_trace t U) d) <= length U)%nat).
{ apply NoDup_incl_length; [apply NoDup_filter; exact ND|]. intros t Ht. apply filter_In in Ht as [_ Ht]. exact (mem_trace_In _ _ Ht). }
unfold wild. rewrite (E d). lia.
Qed.
Lemma depot_inv_len : forall U n d, universe_ok U -> depot_inv U n d -> Z.of_nat (length d) <= DEPOT_MAX + WILD_MAX.
Proof. intros U n d HU (ND & _ & W). pose proof (depot_len_split U d ND HU). lia. Qed.
Lemma depot_inv_cap : forall U n d, universe_ok U -> depot_inv U n d -> Z.of_nat (length d) <= DEPOT_CAP.
Proof. intros U n d HU H. pose proof (depot_inv_len U n d HU H). pose proof depot_cap_ok. lia. Qed.
Lemma depot_inv_frames : forall U n d, depot_inv U n d ->
0 <= fold_right (fun t acc => Z.of_nat (length t) + 1 + acc) 0 d <= 31 * Z.of_nat (length d).
Proof.
intros U n d (_ & HF & _). induction HF as [|t l Ht Hl IH]; cbn [fold_right length]; [lia|].
unfold kUnwindMax in Ht. rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma tr_admit_len : forall U s tr, universe_ok U -> tr_admit U s tr -> (length tr <= kUnwindMax)%nat.
Proof. intros U s tr (_ & HF & _) [H|[H _]]; [exact (proj1 (Forall_forall _ _) HF tr H) | exact H]. Qed.
Lemma depot_inv_mono : forall U n n' d, depot_inv U n d -> n <= n' -> depot_inv U n' d.
Proof. intros U n n' d (ND & HF & W) Hn. split; [exact ND | split; [exact HF | lia]]. Qed.
Fixpoint run_elems (lo sz : Z) (k : nat) : list Z :=
match k with O => [] | S k' => lo :: run_elems (lo + sz) sz k' end.
Definition fseg_elems (sz : Z) (f : fseg) : list Z :=
match f with FRun lo k => run_elems lo sz (Z.to_nat k) | FOne o => [o] end.
Definition fa_elems (sz : Z) (l : list fseg) : list Z := flat_map (fseg_elems sz) l.
Definition chunk_offs (s : astate) (c : Z) : list Z :=
flat_map (fun k => match ck_beg k with
| PPrim off => if prim_class off =? c then [off - region_off c] else []
| _ => []
end) (st_chunks s).
Definition all_batches (s : astate) : list batch := qc_list (st_qthread s) ++ qc_list (st_qglobal s).
Definition batch_offs (s : astate) (c : Z) : list Z :=
if c =? kBatchClass then map (fun b => b_self b - region_off kBatchClass) (all_batches s) else [].
Definition class_elems (s : astate) (c : Z) : list Z :=
fa_elems (class_size c) (rg_free (reg s c)) ++ pc_chunks (cache s c) ++ chunk_offs s c ++ batch_offs s c.
Definition cdef (s : astate) (c : Z) : Z := rg_alloc_user (reg s c) - class_size c * Z.of_nat (length (class_elems s c)).
Definition Compl0 (s : astate) : Prop := forall c, 1 <= c <= 31 -> cdef s c = 0.
Definition nrecZ (s : astate) (c : Z) : Z := Z.of_nat (length (chunk_offs s c) + length (batch_offs s c)).
Definition BigP (s : astate) : Prop :=
forall c, 1 <= c <= 31 -> rg_alloc_user (reg s c) = 0 \/ 4 * (rg_alloc_user (reg s c) / class_size c) <= rg_mapped_fa (reg s c).
Definition BigInv (s : astate) : Prop := Compl0 s /\ BigP s.
Definition BigM (cc : Z) (s : astate) : Prop := BigP s /\ Z.of_nat (length (st_chunks s)) + cc <= 2 ^ 23.
Definition preg (s : astate) (c : Z) : Prop :=
st_nev s <= EV_MAX \/ (cdef s c = 0 /\ class_size c * (nrecZ s c + 8) + 2 ^ 20 <= kUserMapSize * EV_MAX /\ nrecZ s c + 10248 <= 65536).
Lemma preg_small : forall s c, st_nev s <= EV_MAX -> preg s c. Proof. intros s c H. left. exact H. Qed.
Definition regime_big (s : astate) : Prop :=
BigInv s /\
(forall c, 1 <= c <= 31 -> class_size c * (nrecZ s c + 8) + 2 ^ 20 <= kUserMapSize * EV_MAX /\ nrecZ s c + 10248 <= 65536) /\
Z.of_nat (length (st_sec_arr s)) < kPtrArrayEntriesPerCommit /\
(Z.of_nat (length (st_chunks s)) + 1 <= 2 ^ 23 /\ qc_bytes (st_qglobal s) + qc_bytes (st_qthread s) + 2 ^ 29 <= 2 ^ 36).
Definition regime_ok (s : astate) : Prop := st_nev s < EV_MAX \/ regime_big s.
Definition cw (k : chunk) : Z := match ck_beg k with PPrim _ => Z.max 0 (class_size (chunk_class (ck_req k))) | _ => 0 end.
Definition crw (l : list chunk) : Z := fold_right (fun k acc => cw k + acc) 0 l.
Definition rbytes (s : astate) : Z := crw (st_chunks s) + kBatchBytes * Z.of_nat (length (all_batches s)).
Definition SEC_LEN_MAX : Z := 2 ^ 28 + 2 ^ 14.
Definition sec_hulls (s : astate) : Z := fold_right (fun sm acc => sm_len sm / 8 + 8192 + acc) 0 (st_secs s).
Lemma sec_hulls_app1 : forall l sm, fold_right (fun sm acc => sm_len sm / 8 + 8192 + acc) 0 (l ++ [sm])
= fold_right (fun sm acc => sm_len sm / 8 + 8192 + acc) 0 l + (sm_len sm / 8 + 8192).
Proof. intros l sm. induction l as [|x t IH]; cbn [app fold_right]; [lia | rewrite IH; lia]. Qed.
Definition hgrow (s : astate) (n : Z) (s' : astate) : Prop :=
sec_hulls s' <= sec_hulls s + (if from_primary n then 0 else sec_map_size n / 8 + 8192).
Definition mgrow (s : astate) (n : Z) (s' : astate) : Prop :=
Z.of_nat (length (st_chunks s')) <= Z.of_nat (length (st_chunks s)) + 1 /\
crw (st_chunks s') <= crw (st_chunks s) + (if from_primary n then class_size (chunk_class n) else 0) /\
Z.of_nat (length (st_secs s')) <= Z.of_nat (length (st_secs s)) + (if from_primary n then 0 else 1) /\
st_qthread s' = st_qthread s /\ st_qglobal s' = st_qglobal s /\
hgrow s n s'                                          .
Definition fgrow (s s' : astate) : Prop :=
Z.of_nat (length (st_chunks s')) <= Z.of_nat (length (st_chunks s)) /\
crw (st_chunks s') <= crw (st_chunks s) /\
length (st_secs s') = length (st_secs s) /\
Z.of_nat (length (all_batches s')) <= Z.of_nat (length (all_batches s)) + 1.
Lemma crw_app : forall l1 l2, crw (l1 ++ l2) = crw l1 + crw l2.
Proof. intros l1 l2. unfold crw. induction l1 as [|k t IH]; cbn [app fold_right]; [lia | rewrite IH; lia]. Qed.
Lemma cw_nonneg : forall k, 0 <= cw k. Proof. intros k. unfold cw. destruct (ck_beg k); lia. Qed.
Definition EV_BIG : Z := 2 ^ 17.
Definition HPOT_MAX : Z := 3 * 2 ^ 36.
Definition aregime (s : astate) : Prop :=
st_nev s < EV_MAX \/ (regime_big s /\ st_nev s < EV_BIG /\ sec_hulls s <= HPOT_MAX).
Definition aregime_mid (s : astate) : Prop :=
st_nev s <= EV_MAX \/ (st_nev s <= EV_BIG /\ sec_hulls s <= HPOT_MAX /\ Z.of_nat (length (st_chunks s)) <= 2 ^ 23).
Lemma aregime_small : forall s, st_nev s < EV_MAX -> aregime s. Proof. intros s H. left. exact H. Qed.
Lemma aregime_ok : forall s, aregime s -> regime_ok s. Proof. intros s [H|[H _]]; [left | right]; exact H. Qed.
Lemma aregime_to_mid : forall s, aregime s -> aregime_mid s.
Proof. intros s [H|((_ & _ & _ & HC & _) & HE & HH)]; [left; lia | right; repeat split; lia]. Qed.
Definition q_items (s : astate) : list chunk := flat_map b_items (all_batches s).
Definition sum_bytes (l : list batch) : Z := fold_right (fun b acc => b_bytes b + acc) 0 l.
Definition is_alloc (k : chunk) : bool := match ck_state k with CAllocated => true | _ => false end.
Definition blocks (s : astate) : list (sptr * Z) :=
map (fun k => (ck_user k, ck_req k)) (filter is_alloc (st_chunks s)).
Definition frames (s : astate) : list (Z * Z) := fs_live (st_fs s).
Fixpoint count_cid (cid : Z) (l : list (Z * Z)) : Z :=
match l with [] => 0 | (c, _) :: t => (if c =? cid then 1 else 0) + count_cid cid t end.
Definition sec_live_bytes (s : astate) : Z :=
fold_right (fun k acc => match ck_beg k with PSec _ _ => sec_map_size (ck_req k) + acc | _ => acc end) 0 (st_chunks s).
Definition prim_committed (s : astate) : Z :=
fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 (st_regions s).
Definition prim_user_mapped (s : astate) : Z :=
fold_right (fun r acc => rg_mapped_user r + acc) 0 (st_regions s).
Definition blocks_bytes (s : astate) : Z :=
fold_right (fun k acc => if is_alloc k then ck_req k + acc else acc) 0 (st_chunks s).
Definition LIVE_MAX : Z := 2 ^ 34.
Definition items_n (l : list chunk) : Z := fold_right (fun k acc => ck_n k + acc) 0 l.
Definition quar_nl (l : list chunk) : Z := fold_right (fun k acc => if is_alloc k then acc else ck_n k + acc) 0 l.
Definition quar_n (s : astate) : Z := quar_nl (st_chunks s).
Definition queued_n (s : astate) : Z := items_n (q_items s).
Definition qtight (s : astate) : Prop :=
qc_bytes (st_qthread s) <= kQuarantineCacheMax /\ qc_bytes (st_qglobal s) <= kQuarantineMax /\ quar_n s <= queued_n s.
Definition qloose (s : astate) : Prop :=
qc_bytes (st_qthread s) <= 2 ^ 29 /\ qc_bytes (st_qglobal s) <= 2 ^ 30 /\ quar_n s <= queued_n s + 2 ^ 30.
Lemma items_n_app : forall l1 l2, items_n (l1 ++ l2) = items_n l1 + items_n l2.
Proof. intros l1 l2. unfold items_n. induction l1 as [|k t IH]; cbn; [lia | rewrite IH; lia]. Qed.
Lemma quar_nl_app : forall l1 l2, quar_nl (l1 ++ l2) = quar_nl l1 + quar_nl l2.
Proof. intros l1 l2. unfold quar_nl. induction l1 as [|k t IH]; cbn; [lia | rewrite IH; destruct (is_alloc k); lia]. Qed.
Lemma qtight_qloose : forall s, qtight s -> qloose s.
Proof. intros s (A & B & C). unfold qloose, kQuarantineCacheMax, kQuarantineMax in *. lia. Qed.
Lemma qtight_ext : forall s0 s,
st_chunks s = st_chunks s0 -> st_qthread s = st_qthread s0 -> st_qglobal s = st_qglobal s0 -> qtight s0 -> qtight s.
Proof.
intros s0 s H1 H2 H3 Q. unfold qtight, quar_n, queued_n, q_items, all_batches in *. rewrite H1, H2, H3. exact Q.
Qed.
Lemma qloose_ext : forall s0 s,
st_chunks s = st_chunks s0 -> st_qthread s = st_qthread s0 -> st_qglobal s = st_qglobal s0 -> qloose s0 -> qloose s.
Proof.
intros s0 s H1 H2 H3 Q. unfold qloose, quar_n, queued_n, q_items, all_batches in *. rewrite H1, H2, H3. exact Q.
Qed.
Lemma qtight_alloc_app : forall s0 s k,
st_chunks s = st_chunks s0 ++ [k] -> is_alloc k = true -> st_qthread s = st_qthread s0 -> st_qglobal s = st_qglobal s0 ->
qtight s0 -> qtight s.
Proof.
intros s0 s k H1 Hk H2 H3 Q. unfold qtight, quar_n, queued_n, q_items, all_batches in *. rewrite H1, H2, H3, quar_nl_app.
unfold quar_nl at 2. cbn [fold_right]. rewrite Hk. rewrite Z.add_0_r. exact Q.
Qed.
Section WF.
Variable U : list (list Z).
Definition hole_ok (r : region) (h : Z * Z) : Prop := False.
Record cls_ok (c : Z) (r : region) (p : pclass) (inited : bool) (ko bo : list Z) : Prop := {
wr_alloc : 0 <= rg_alloc_user r <= rg_mapped_user r;
wr_carved : rg_mapped_user r - rg_alloc_user r < kUserMapSize + kMaxSize;
wr_mapped_al : rg_mapped_user r mod kUserMapSize = 0;
wr_alloc_al : rg_alloc_user r mod class_size c = 0;
wr_fa : 0 <= rg_mapped_fa r /\ rg_mapped_fa r mod kFreeArrayMapSize = 0;
wr_fa_bound : rg_mapped_fa r <= kFreeArrayMax;
wr_fa_len : 4 * fa_len (rg_free r) <= rg_mapped_fa r;
wr_runs : Forall (fun f => match f with FRun lo k => 1 <= k | FOne _ => True end) (rg_free r);
wr_nodup : NoDup (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo);
wr_elems : Forall (fun o => 0 <= o < rg_alloc_user r /\ o mod class_size c = 0) (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo);
wr_holes : Forall (hole_ok r) (rg_holes r) /\ NoDup (rg_holes r);
wr_cache : if inited then pc_max p = max_cached c /\ Z.of_nat (length (pc_chunks p)) <= max_cached c else p = pclass0;
wr_mapped_bound : rg_mapped_user r <= kUserMapSize * EV_MAX
}.
Definition wf_class (s : astate) (c : Z) : Prop :=
cls_ok c (reg s c) (cache s c) (st_cache_inited s) (chunk_offs s c) (batch_offs s c).
Lemma class_elems_eq : forall s c,
class_elems s c = fa_elems (class_size c) (rg_free (reg s c)) ++ pc_chunks (cache s c) ++ chunk_offs s c ++ batch_offs s c.
Proof. reflexivity. Qed.
Definition chunk_ok (s : astate) (k : chunk) : Prop :=
0 <= ck_req k < MALLOC_MAX /\
match ck_beg k with
| PPrim off => from_primary (ck_req k) = true /\ prim_class off = chunk_class (ck_req k) /\
0 <= off - region_off (prim_class off) < 2 ^ 32
| PSec r off => from_primary (ck_req k) = false /\ off = kPage /\
exists sm, nth_error (st_secs s) r = Some sm /\ sm_live sm = true /\
sm_size sm = needed_size (ck_req k) /\ sm_len sm = sec_map_size (ck_req k)
| _ => False
end.
Definition bfull (b : batch) : Prop := length (b_items b) = Z.to_nat kBatchSlots.
Definition qgroup_ok (g : list batch) : Prop := g <> [] /\ Forall bfull (removelast g) /\ kQuarantineCacheMax < sum_bytes g.
Record wf_quar (s : astate) : Prop := {
wq_bytes_t : qc_bytes (st_qthread s) = sum_bytes (qc_list (st_qthread s));
wq_bytes_g : qc_bytes (st_qglobal s) = sum_bytes (qc_list (st_qglobal s));
wq_batches : Forall (fun b => (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) (all_batches s);
wq_items : Forall (fun k => In k (st_chunks s) /\ ck_state k = CQuarantined) (q_items s);
wq_nodup : NoDup (map ck_beg (q_items s));
wq_tfull : Forall bfull (removelast (qc_list (st_qthread s)));
wq_groups : exists F GS, qc_list (st_qglobal s) = F ++ concat GS /\ Forall bfull (removelast F) /\ Forall qgroup_ok GS
}.
Record wf_sec (s : astate) : Prop := {
ws_nodup : NoDup (st_sec_arr s);
ws_arr_chunks : forall r, In r (st_sec_arr s) <-> exists k, In k (st_chunks s) /\ ck_beg k = PSec r kPage;
ws_arr_live : forall r, In r (st_sec_arr s) <->
exists sm, nth_error (st_secs s) r = Some sm /\ sm_live sm = true;
ws_reserved : Z.of_nat (length (st_sec_arr s)) <= st_sec_reserved s <= kPtrArrayEntriesPerCommit;
ws_reserved_al : 0 <= st_sec_reserved s /\ st_sec_reserved s mod kPtrArrayEntriesPerCommit = 0;
ws_lens : Forall (fun sm => 0 <= sm_len sm <= SEC_LEN_MAX) (st_secs s)
}.
Record wf_fs (s : astate) : Prop := {
wfs_hints : length (fs_hint (st_fs s)) = 11%nat /\ Forall (fun h => 0 <= h) (fs_hint (st_fs s));
wfs_nodup : NoDup (fs_live (st_fs s));
wfs_live : Forall (fun cp => 0 <= fst cp <= 10 /\ 0 <= snd cp < fs_frames (fst cp)) (fs_live (st_fs s))
}.
Definition fa_room (alloc : Z) (len : nat) (k : Z) (mfa : Z) : Prop := alloc = 0 \/ 4 * (Z.of_nat len + k) <= mfa.
Definition bslack (c bb : Z) : Z := if c =? kBatchClass then bb else 0.
Lemma bslack_24 : forall bb, bslack kBatchClass bb = bb. Proof. intros bb. unfold bslack. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma bslack_other : forall c bb, c <> kBatchClass -> bslack c bb = 0.
Proof. intros c bb H. unfold bslack. destruct (Z.eqb_spec c kBatchClass); [lia | reflexivity]. Qed.
Lemma bslack_mono : forall c bb bb', 0 <= bb' <= bb -> 0 <= bslack c bb' <= bslack c bb.
Proof. intros c bb bb' H. unfold bslack. destruct (c =? kBatchClass); lia. Qed.
Lemma bslack_le : forall c bb, 0 <= bb -> 0 <= bslack c bb <= bb.
Proof. intros c bb H. unfold bslack. destruct (c =? kBatchClass); lia. Qed.
Record WfP (pp cc bb : Z) (s : astate) : Prop := {
wf_len_regions : length (st_regions s) = 32%nat;
wf_len_cache : length (st_cache s) = 32%nat;
wf_reg0 : reg s 0 = region0;
wf_classes : forall c, 1 <= c <= 31 -> wf_class s c;
wf_chunks : Forall (chunk_ok s) (st_chunks s);
wf_chunks_nodup : NoDup (map ck_beg (st_chunks s));
wf_chunks_ev : Z.of_nat (length (st_chunks s)) + cc <= st_nev s;
wf_prim_ev : prim_user_mapped s + kUserMapSize * pp <= kUserMapSize * st_nev s;
wf_live : blocks_bytes s <= LIVE_MAX;
wf_quarantine : wf_quar s;
wf_batches_ev : Z.of_nat (length (all_batches s)) + bb <= st_nev s;
wf_secondary : wf_sec s;
wf_fakestack : wf_fs s;
wf_depot : depot_inv U (st_nev s) (st_depot s);
wf_nev : 0 <= st_nev s;
wf_slack : 0 <= pp /\ 0 <= cc /\ 0 <= bb;
wf_qinited : all_batches s <> [] -> st_cache_inited s = true;
wf_fa_room : forall c, 1 <= c <= 31 ->
fa_room (rg_alloc_user (reg s c)) (length (class_elems s c)) (cc + bslack c bb + 2 * (EV_MAX - st_nev s)) (rg_mapped_fa (reg s c));
wf_secs_ev : Z.of_nat (length (st_secs s)) + cc <= st_nev s;
wf_regime : st_nev s <= EV_MAX \/ BigM cc s
}.
Definition Wf : astate -> Prop := WfP 0 0 0.
End WF.
Lemma reg_init : forall c, reg init_state c = region0.
Proof.
intros c. unfold reg, znth, init_state. cbn -[nth repeat].
destruct (nth_in_or_default (Z.to_nat c) (repeat region0 32) region0) as [H| ->]; [apply repeat_spec in H; exact H | reflexivity].
Qed.
Lemma cache_init : forall c, cache init_state c = pclass0.
Proof.
intros c. unfold cache, znth, init_state. cbn -[nth repeat].
destruct (nth_in_or_default (Z.to_nat c) (repeat pclass0 32) pclass0) as [H| ->]; [apply repeat_spec in H; exact H | reflexivity].
Qed.
Lemma class_elems_init : forall c, class_elems init_state c = [].
Proof.
intros c. unfold class_elems, chunk_offs, batch_offs, all_batches. rewrite reg_init, cache_init. cbn.
destruct (c =? kBatchClass); reflexivity.
Qed.
Ltac kc := unfold kMaxSize, kNumClasses, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArrayMax,
kChunkHeaderSize, kChunkHeader2Size, kPage, kSecRz, kPtrArrayCommit, kPtrArrayEntriesPerCommit, kMaxNumChunks,
kBatchClass, kBatchBytes, kBatchSlots, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax,
kClearShadowMmapThreshold, kMallocFill, kMaxAllowedMalloc, kStackSizeLog, kDepotIdsPerBlock, kStoreFramesPerBlock,
kUnwindMax, EV_MAX, MALLOC_MAX, DEPOT_MAX, LIVE_MAX, kStartFramesMax in *.
Theorem wf_init : forall U, Wf U init_state.
Proof.
intros U. unfold Wf. constructor.
- reflexivity.
- reflexivity.
- apply reg_init.
- intros c Hc. pose proof (class_ok c Hc) as (K1 & K2 & _). unfold wf_class. rewrite reg_init, cache_init.
assert (E : chunk_offs init_state c = [] /\ batch_offs init_state c = []).
{ unfold chunk_offs, batch_offs, all_batches. cbn. split; [reflexivity | destruct (c =? kBatchClass); reflexivity]. }
destruct E as [-> ->].
constructor; cbn -[Z.mul Z.div Z.modulo Z.add Z.le Z.lt]; try (kc; lia).
+ reflexivity.
+ rewrite Z.mod_0_l; [reflexivity | lia].
+ split; [lia | reflexivity].
+ constructor.
+ constructor.
+ constructor.
+ split; constructor.
+ reflexivity.
- constructor.
- constructor.
- cbn. lia.
- cbn. lia.
- cbn. kc. lia.
- constructor; cbn; try lia; try constructor; kc; try lia.
exists [], []. cbn. split; [reflexivity | split; constructor].
- cbn. lia.
- constructor; cbn.
+ constructor.
+ intros r. split; [intros [] | intros (k & [] & _)].
+ intros r. split; [intros [] | intros (sm & H & _)]. destruct r; discriminate.
+ kc. lia.
+ split; [lia | reflexivity].
+ constructor.
- constructor; cbn.
+ split; [reflexivity|]. repeat constructor; lia.
+ constructor.
+ constructor.
- unfold depot_inv. cbn. split; [constructor | split; [constructor | lia]].
- cbn. kc. lia.
- lia.
- intros H. exfalso. apply H. reflexivity.
- intros c Hc. left. rewrite reg_init. reflexivity.
- cbn. lia.
- left. cbn. unfold EV_MAX. lia.
Qed.
Lemma BigInv_init : BigInv init_state.
Proof.
split.
- intros c Hc. unfold cdef. rewrite reg_init, class_elems_init. cbn. lia.
- intros c Hc. left. rewrite reg_init. reflexivity.
Qed.
Lemma regime_big_init : regime_big init_state.
Proof.
unfold regime_big. split; [exact BigInv_init|]. split; [|split; [|split]].
- intros c Hc. pose proof (class_ok c Hc) as (K1 & _ & K3 & _).
assert (E : nrecZ init_state c = 0) by (unfold nrecZ, chunk_offs, batch_offs, all_batches; cbn; destruct (c =? kBatchClass); reflexivity).
rewrite E. unfold kMaxSize, kUserMapSize, EV_MAX in *. lia.
- cbn. unfold kPtrArrayEntriesPerCommit. lia.
- cbn. lia.
- cbn. lia.
Qed.
Lemma fa_room_mono : forall alloc len k mfa len' k' mfa',
fa_room alloc len k mfa -> (len' <= len)%nat -> k' <= k -> mfa <= mfa' -> fa_room alloc len' k' mfa'.
Proof. intros alloc len k mfa len' k' mfa' [H|H] L K M; [left; exact H | right; lia]. Qed.
Lemma fa_room_xfer : forall alloc len k mfa len' k' mfa',
fa_room alloc len k mfa -> Z.of_nat len' + k' <= Z.of_nat len + k -> mfa <= mfa' -> fa_room alloc len' k' mfa'.
Proof. intros alloc len k mfa len' k' mfa' [H|H] L M; [left; exact H | right; lia]. Qed.
Lemma qtight_init : qtight init_state.
Proof. unfold qtight, quar_n, queued_n, q_items, all_batches. cbn. kc. lia. Qed.
Definition secs_ext (s s' : astate) : Prop :=
forall r sm, nth_error (st_secs s) r = Some sm ->
exists sm', nth_error (st_secs s') r = Some sm' /\ sm_len sm' = sm_len sm /\ sm_size sm' = sm_size sm.
Lemma secs_ext_refl : forall s, secs_ext s s.
Proof. intros s r sm H. exists sm. auto. Qed.
Lemma secs_ext_trans : forall s1 s2 s3, secs_ext s1 s2 -> secs_ext s2 s3 -> secs_ext s1 s3.
Proof.
intros s1 s2 s3 H12 H23 r sm H. destruct (H12 r sm H) as (sm2 & H2 & L2 & S2).
destruct (H23 r sm2 H2) as (sm3 & H3 & L3 & S3). exists sm3. rewrite L3, S3. auto.
Qed.
Definition malloc_post (U : list (list Z)) (s : astate) (n : Z) (ns : bool) (r : sptr * astate) : Prop :=
let (p, s') := r in
Wf U s' /\ st_nev s' = st_nev s + 1 /\ secs_ext s s' /\ frames s' = frames s /\
match p with
| PNull => blocks s' = blocks s
| _ => blocks s' = blocks s ++ [(p, n)] /\ ~ In p (map fst (blocks s))
end /\
(qtight s -> qtight s')           .
Definition free_post (U : list (list Z)) (s : astate) (p : sptr) (n : Z) (ns : bool) (r : unit * astate) : Prop :=
let s' := snd r in
Wf U s' /\ st_nev s' = st_nev s + 1 /\ secs_ext s s' /\ frames s' = frames s /\
(exists l1 l2, ((p = PNull /\ l1 ++ l2 = blocks s) \/ blocks s = l1 ++ (p, n) :: l2) /\ blocks s' = l1 ++ l2) /\
(qtight s -> qtight s')           .
Definition stack_malloc_post (U : list (list Z)) (s : astate) (cid : Z) (ns : bool) (r : sptr * astate) : Prop :=
let (p, s') := r in
Wf U s' /\ (exists f, s' = set_fs f s) /\
match p with
| PFake c pos => c = cid /\ 0 <= pos < fs_frames cid /\ frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s)
| PNull => s' = s
| _ => False
end.
Definition stack_free_state (cid pos : Z) (s : astate) : astate :=
set_fs (mkFS (fs_hint (st_fs s)) (del_pos (fs_live (st_fs s)) cid pos)) s.
Definition stack_free_post (U : list (list Z)) (s : astate) (cid pos : Z) : Prop :=
Wf U (stack_free_state cid pos s) /\
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Lemma blocks_set_fs : forall f s, blocks (set_fs f s) = blocks s. Proof. reflexivity. Qed.
Lemma blocks_stack_free_state : forall cid pos s, blocks (stack_free_state cid pos s) = blocks s. Proof. reflexivity. Qed.
