(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Ltac cbnr := cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd].
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Lemma trace_eqb_eq : forall a b, trace_eqb a b = true <-> a = b.
Proof.
induction a as [|x a IH]; intros [|y b]; cbn; try (split; [discriminate | congruence]).
- split; reflexivity.
- rewrite Bool.andb_true_iff, Z.eqb_eq, IH. split; [intros [-> ->]; reflexivity | intros H; injection H; auto].
Qed.
Lemma mem_trace_false : forall t l, mem_trace t l = false -> ~ In t l.
Proof.
intros t l. induction l as [|u l IH]; cbn; [tauto|]. rewrite Bool.orb_false_iff. intros [H1 H2] [E|Hin].
- subst u. rewrite (proj2 (trace_eqb_eq t t) eq_refl) in H1. discriminate.
- exact (IH H2 Hin).
Qed.
Lemma depot_frames_bound : forall (l : list (list Z)), Forall (fun t => (length t <= kUnwindMax)%nat) l ->
0 <= fold_right (fun t acc => Z.of_nat (length t) + 1 + acc) 0 l <= 31 * Z.of_nat (length l).
Proof.
intros l H. induction H as [|t l Ht Hl IH]; cbn [fold_right length]; [lia|].
unfold kUnwindMax in Ht. rewrite Nat2Z.inj_succ. lia.
Qed.
Definition depot_post (U : list (list Z)) (s : astate) (tr : list Z) (ns : bool) (res : unit * astate) : Prop :=
let (_, s') := res in exists d, s' = set_depot d s /\ NoDup d /\ incl d U /\ (d = st_depot s \/ d = st_depot s ++ [tr]) /\ ns = true.
Lemma depot_put_ok : forall U s tr ns,
NoDup (st_depot s) -> incl (st_depot s) U -> universe_ok U -> In tr U ->
atok ns (depot_put tr s) (depot_post U s tr).
Proof.
intros U s tr ns Hnd Hincl (HU1 & HU2 & HU3) Hin.
assert (Hlen : (length (st_depot s) <= length U)%nat) by (apply NoDup_incl_length; assumption).
assert (ES : set_depot (st_depot s) s = s) by (destruct s; reflexivity).
unfold depot_put. apply atok_bind. apply atok_askz.
{ cbn. exact (proj1 (Forall_forall _ _) HU2 tr Hin). }
intros z Hz. cbn [fst snd progz]. destruct (Z.eqb_spec z 0) as [->|Hnz].
- apply atok_ret. exists (st_depot s). rewrite ES. splits; auto.
- cbn in Hz. destruct Hz as [->|[-> Hmt]]; [lia|].
apply atok_bind. apply atok_get. cbn [fst snd].
pose proof (depot_frames_bound (st_depot s) ltac:(apply Forall_forall; intros t Ht; apply (proj1 (Forall_forall _ _) HU2); apply Hincl; exact Ht)) as FB.
pose proof (proj1 (Forall_forall _ _) HU2 tr Hin) as Htr.
apply atok_bind. apply atok_mcheck.
{ apply Z.ltb_lt. unfold depot_ids, kDepotIdsPerBlock, DEPOT_MAX in *. lia. }
cbn [fst snd]. apply atok_bind. apply atok_mcheck.
{ apply Z.ltb_lt. unfold depot_frames, kStoreFramesPerBlock, kStartFramesMax, DEPOT_MAX, kUnwindMax in *. lia. }
cbn [fst snd]. apply atok_put. exists (st_depot s ++ [tr]). splits; auto.
+ apply NoDup_app_iff. split; [exact Hnd|]. split; [repeat constructor; intros []|].
intros x Hx [<-|[]]. exact (mem_trace_false _ _ Hmt Hx).
+ intros x Hx. apply in_app_iff in Hx as [Hx|[<-|[]]]; [apply Hincl; exact Hx | exact Hin].
Qed.
Lemma WfP_set_depot : forall U pp cc bb s d,
WfP U pp cc bb s -> NoDup d -> incl d U -> WfP U pp cc bb (set_depot d s).
Proof.
intros U pp cc bb s d W Hnd Hincl. wf_fields W. constructor; wf_easy.
cbn. split; assumption.
Qed.
Lemma nth_error_app_l {X} : forall (l1 l2 : list X) i, (i < length l1)%nat -> nth_error (l1 ++ l2) i = nth_error l1 i.
Proof. intros. apply nth_error_app1. assumption. Qed.
Lemma nth_error_lt {X} : forall (l : list X) i x, nth_error l i = Some x -> (i < length l)%nat.
Proof. intros l i x H. destruct (Nat.lt_ge_cases i (length l)) as [Hl|Hl]; [exact Hl|]. rewrite (proj2 (nth_error_None l i) Hl) in H. discriminate. Qed.
Lemma chunk_ok_app_secs : forall s l k, chunk_ok s k -> chunk_ok (set_secs (st_secs s ++ l) s) k.
Proof.
intros s l k H. unfold chunk_ok in *. destruct H as [H1 H2]. split; [exact H1|].
destruct (ck_beg k); try exact H2. destruct H2 as (A & B & sm & E & C). split; [exact A|]. split; [exact B|].
exists sm. cbn. rewrite nth_error_app_l by (eapply nth_error_lt; exact E). split; [exact E | exact C].
Qed.
Lemma blocks_bytes_set : forall s f, (forall s, st_chunks (f s) = st_chunks s) -> blocks_bytes (f s) = blocks_bytes s.
Proof. intros s f H. unfold blocks_bytes. rewrite H. reflexivity. Qed.
Lemma sec_arr_length : forall U pp cc bb s, WfP U pp cc bb s -> (length (st_sec_arr s) <= length (st_chunks s))%nat.
Proof.
intros U pp cc bb s W. pose proof (wf_secondary _ _ _ _ _ W) as X. destruct X as [Snd Sac _ _ _].
rewrite <- (length_map (fun r => PSec r kPage) (st_sec_arr s)), <- (length_map ck_beg (st_chunks s)).
apply NoDup_incl_length.
- apply NoDup_map_NoDup_ForallPairs; [|exact Snd]. intros a b _ _ H. injection H. auto.
- intros p Hp. apply in_map_iff in Hp as (r & <- & Hr). apply Sac in Hr as (k & Hk & Hb). apply in_map_iff. exists k. auto.
Qed.
Lemma sec_map_size_range : forall n, 0 <= n < MALLOC_MAX -> 0 <= sec_map_size n <= SEC_LEN_MAX.
Proof.
intros n Hn. unfold sec_map_size, needed_size, SEC_LEN_MAX.
pose proof (needed_primary_bounds n ltac:(lia)) as (N1 & N2 & N3). pose proof (rz_size_bounds n) as [R1 R2]. pose proof (req_size_bounds n ltac:(lia)) as (_ & Q1 & Q2 & Q3).
assert (RU : forall x, 0 <= x -> x <= round_up x kPage < x + kPage).
{ intros x Hx. unfold round_up, kPage. pose proof (Z.mul_div_le (x + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)).
pose proof (Z.div_mod (x + 4096 - 1) 4096 ltac:(lia)). lia. }
unfold MALLOC_MAX in *.
destruct (from_primary n); [pose proof (RU (needed_primary n) ltac:(lia)) | pose proof (RU (needed_primary n + rz_size n) ltac:(lia))]; unfold kPage in *; lia.
Qed.
Lemma WfP_add_sec : forall U pp cc bb s n d res',
WfP U pp cc bb s -> 1 <= cc -> 0 <= n < MALLOC_MAX -> from_primary n = false -> blocks_bytes s + n <= LIVE_MAX ->
NoDup d -> incl d U ->
Z.of_nat (length (st_sec_arr s)) < kPtrArrayEntriesPerCommit ->
((res' = st_sec_reserved s /\ Z.of_nat (length (st_sec_arr s)) < st_sec_reserved s) \/
(res' = st_sec_reserved s + kPtrArrayEntriesPerCommit /\ Z.of_nat (length (st_sec_arr s)) = st_sec_reserved s)) ->
let r := length (st_secs s) in
let sm := mkSec (sec_map_size n) (needed_size n) true in
WfP U pp (cc - 1) bb
(set_chunks (st_chunks s ++ [mkChunk (PSec r kPage) n CAllocated])
(set_depot d (set_sec_arr (st_sec_arr s ++ [r]) (set_sec_reserved res' (set_secs (st_secs s ++ [sm]) s))))).
Proof.
intros U pp cc bb s n d res' W Hcc Hn Hprim Hlive Hnd Hincl HSEC Hres r sm.
wf_fields W. sec_fields Xsec.
assert (Hfresh : forall k, In k (st_chunks s) -> forall o, ck_beg k <> PSec r o).
{ intros k Hk o E. pose proof (proj1 (Forall_forall _ _) Xck k Hk) as [_ CK]. rewrite E in CK.
destruct CK as (_ & _ & sm' & Es & _). apply nth_error_lt in Es. subst r. lia. }
assert (Hr_notin : ~ In r (st_sec_arr s)).
{ intros Hin. apply Sac in Hin as (k & Hk & Hb). exact (Hfresh k Hk _ Hb). }
constructor; wf_easy.
- intros c' Hc'. unfold wf_class.
change (chunk_offs ?[S] c') with (chunk_offs (set_chunks (st_chunks s ++ [mkChunk (PSec r kPage) n CAllocated]) s) c').
rewrite chunk_offs_app. unfold chunk_offs at 2. cbn [st_chunks set_chunks flat_map ck_beg app]. rewrite app_nil_r.
exact (Xcl c' Hc').
- cbn [st_chunks set_chunks set_depot set_sec_arr set_sec_reserved set_secs]. apply Forall_app. split.
+ eapply Forall_impl; [|exact Xck]. intros k Hk. apply (chunk_ok_app_secs s [sm] k) in Hk.
unfold chunk_ok in *. cbn [st_secs set_chunks set_depot set_sec_arr set_sec_reserved set_secs] in *. exact Hk.
+ constructor; [|constructor]. unfold chunk_ok. cbn [ck_req ck_beg st_secs set_chunks set_depot set_sec_arr set_sec_reserved set_secs].
split; [lia|]. split; [exact Hprim|]. split; [reflexivity|]. exists sm. subst r.
rewrite nth_error_app2, Nat.sub_diag by lia. cbn. repeat split; reflexivity.
- cbn [st_chunks set_chunks set_depot set_sec_arr set_sec_reserved set_secs]. rewrite map_app. cbn [map ck_beg].
apply NoDup_app_iff. split; [exact Xnd|]. split; [repeat constructor; intros []|].
intros x Hx [<-|[]]. apply in_map_iff in Hx as (k & Hb & Hk). exact (Hfresh k Hk _ Hb).
- cbn [st_chunks st_nev set_chunks set_depot set_sec_arr set_sec_reserved set_secs]. rewrite length_app. cbn [length]. lia.
- change (blocks_bytes ?[S]) with (blocks_bytes (set_chunks (st_chunks s ++ [mkChunk (PSec r kPage) n CAllocated]) s)).
rewrite blocks_bytes_app1. cbn [is_alloc ck_state ck_req]. lia.
- quar_fields Xq. constructor; cbn [st_qthread st_qglobal st_chunks set_chunks set_depot set_sec_arr set_sec_reserved set_secs]; try assumption.
+ eapply Forall_impl; [|exact Qit]. intros k [Hk Hs]. split; [apply in_app_iff; left; exact Hk | exact Hs].
- constructor; cbn [st_sec_arr st_secs st_chunks st_sec_reserved set_chunks set_depot set_sec_arr set_sec_reserved set_secs].
+ apply NoDup_app_iff. split; [exact Snd|]. split; [repeat constructor; intros []|]. intros x Hx [<-|[]]. exact (Hr_notin Hx).
+ intros r'. rewrite in_app_iff. cbn [In]. split.
* intros [Hin|[<-|[]]].
-- apply Sac in Hin as (k & Hk & Hb). exists k. split; [apply in_app_iff; left; exact Hk | exact Hb].
-- eexists. split; [apply in_app_iff; right; left; reflexivity | reflexivity].
* intros (k & Hk & Hb). apply in_app_iff in Hk as [Hk|[<-|[]]].
-- left. apply Sac. exists k. auto.
-- cbn in Hb. injection Hb as <-. right. left. reflexivity.
+ intros r'. rewrite in_app_iff. cbn [In]. split.
* intros [Hin|[<-|[]]].
-- pose proof (proj1 (Sal r') Hin) as (sm' & E & L). exists sm'. rewrite nth_error_app_l by (eapply nth_error_lt; exact E). auto.
-- exists sm. subst r. rewrite nth_error_app2, Nat.sub_diag by lia. split; reflexivity.
* intros (sm' & E & L). destruct (Nat.lt_ge_cases r' (length (st_secs s))) as [Hl|Hl].
-- left. apply (proj2 (Sal r')). exists sm'. rewrite nth_error_app_l in E by exact Hl. auto.
-- right. rewrite nth_error_app2 in E by lia. destruct (r' - length (st_secs s))%nat as [|m] eqn:Em; [left; subst r; lia|].
cbn in E. destruct m; discriminate.
+ rewrite length_app. cbn [length]. pose proof (sec_arr_length U pp cc bb s W) as AL.
destruct Sral as [S1 S2]. apply Z.mod_divide in S2 as [q Hq]; [|unfold kPtrArrayEntriesPerCommit; lia].
unfold kPtrArrayEntriesPerCommit, EV_MAX in *. destruct Hres as [[-> Hlt]|[-> Heq]]; [lia|].
assert (q = 0) by nia. subst q. lia.
+ unfold kPtrArrayEntriesPerCommit in *. destruct Hres as [[-> _]|[-> _]]; [exact Sral|].
destruct Sral as [S1 S2]. split; [lia|]. rewrite Z.add_mod, S2, Z.mod_same by lia. reflexivity.
+   apply Forall_app. split; [exact Slen|]. constructor; [|constructor]. subst sm. cbn [sm_len]. exact (sec_map_size_range n Hn).
- cbn. split; assumption.
- lia.
-
intros c' Hc'. eapply fa_room_xfer; [exact (Xroom c' Hc') | | apply Z.le_refl].
match goal with |- Z.of_nat (length (class_elems ?S2 c')) + _ <= _ =>
replace (class_elems S2 c') with (class_elems s c'); [cbn [st_nev set_chunks set_depot set_sec_arr set_sec_reserved set_secs]; lia|] end.
unfold class_elems, chunk_offs. cbn [st_chunks st_regions st_cache st_qthread st_qglobal set_chunks set_depot set_sec_arr set_sec_reserved set_secs].
rewrite flat_map_app. cbn [flat_map ck_beg app]. rewrite app_nil_r. reflexivity.
-
cbn [st_secs st_nev set_chunks set_depot set_sec_arr set_sec_reserved set_secs]. rewrite length_app. cbn [length]. lia.
Qed.
Lemma In_chunk_offs : forall s k off, In k (st_chunks s) -> ck_beg k = PPrim off ->
In (off - region_off (prim_class off)) (chunk_offs s (prim_class off)).
Proof.
intros s k off Hk Hb. unfold chunk_offs. apply in_flat_map. exists k. split; [exact Hk|]. rewrite Hb, Z.eqb_refl. left. reflexivity.
Qed.
Lemma prim_class_window : forall c y, 0 <= c -> 0 <= y < 2 ^ 32 -> prim_class (region_off c + y) = c.
Proof. exact prim_class_region_off. Qed.
Lemma prim_chunk_off : forall U pp cc bb s k off, WfP U pp cc bb s -> In k (st_chunks s) -> ck_beg k = PPrim off ->
let c := prim_class off in
1 <= c <= 30 /\ c = chunk_class (ck_req k) /\ from_primary (ck_req k) = true /\ 0 <= ck_req k /\
0 <= off - region_off c < 2 ^ 31 /\ (off - region_off c) mod class_size c = 0.
Proof.
intros U pp cc bb s k off W Hk Hb c.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W) k Hk) as [CKn CK]. rewrite Hb in CK. destruct CK as (CKp & CKc & CKo).
pose proof (primary_geometry (ck_req k) ltac:(lia) CKp) as (Gc & _).
assert (Hc : 1 <= c <= 30) by (subst c; rewrite CKc; exact Gc).
pose proof (In_chunk_offs s k off Hk Hb) as Hin. fold c in Hin.
pose proof (wf_classes _ _ _ _ _ W c ltac:(lia)) as CL.
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) (off - region_off c)) as E.
specialize (E ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hin)).
pose proof (wr_alloc _ _ _ _ _ _ CL). pose proof (mapped_user_bound U pp cc bb s c W ltac:(lia)).
pose proof (wf_slack _ _ _ _ _ W). unfold kUserMapSize, EV_MAX in *. subst c. splits; try lia. auto.
Qed.
Lemma prim_user_inj : forall U pp cc bb s k boff c x n,
WfP U pp cc bb s -> In k (st_chunks s) -> ck_beg k = PPrim boff ->
1 <= c <= 31 -> 0 <= x < 2 ^ 31 -> x mod class_size c = 0 -> 0 <= n -> from_primary n = true -> chunk_class n = c ->
boff + ck_rz k = region_off c + x + rz_size n -> boff = region_off c + x.
Proof.
intros U pp cc bb s k boff c x n W Hk Hb Hc Hx Hxa Hn Hp Hcn E.
pose proof (prim_chunk_off U pp cc bb s k boff W Hk Hb) as (G1 & G2 & G3 & G4 & G5 & G6). cbv zeta in *.
remember (prim_class boff) as c' eqn:Ec'.
pose proof (rz_size_bounds n) as [Rn _]. pose proof (rz_size_bounds (ck_req k)) as [Rk _]. unfold ck_rz in E.
pose proof (primary_geometry n Hn Hp) as (_ & Sn & _ & _ & Pn). rewrite Hcn in Sn, Pn.
pose proof (primary_geometry (ck_req k) G4 G3) as (_ & Sk & _). rewrite <- G2 in Sk.
pose proof (req_size_bounds n Hn) as (_ & Qn & _). pose proof (req_size_bounds (ck_req k) G4) as (_ & Qk & _).
assert (Ec : c' = c).
{ pose proof (prim_class_region_off c' (boff - region_off c' + rz_size (ck_req k)) ltac:(lia) ltac:(lia)) as P1.
pose proof (prim_class_region_off c (x + rz_size n) ltac:(lia) ltac:(lia)) as P2.
replace (region_off c' + (boff - region_off c' + rz_size (ck_req k))) with (region_off c + (x + rz_size n)) in P1 by lia.
congruence. }
subst c'. rewrite Ec in *.
destruct (Z.eq_dec (boff - region_off c) x) as [Eyx|Ne]; [lia|]. exfalso.
assert (D : (boff - region_off c - x) mod class_size c = 0).
{ rewrite Zminus_mod, G6, Hxa. cbn. first [reflexivity | apply Z.mod_0_l; lia]. }
apply Z.mod_divide in D as [q Hq]; [|lia].
assert (Hq0 : q <> 0) by (intros ->; lia).
assert (Habs : class_size c <= Z.abs (boff - region_off c - x)) by nia. lia.
Qed.
Definition sec_alloc_post (s : astate) (n : Z) (ns : bool) (res : option sptr * astate) : Prop :=
let (o, s') := res in
match o with
| None => s' = s /\ ns = false
| Some p => exists res', p = PSec (length (st_secs s)) kPage /\
s' = set_sec_arr (st_sec_arr s ++ [length (st_secs s)])
(set_sec_reserved res' (set_secs (st_secs s ++ [mkSec (sec_map_size n) (needed_size n) true]) s)) /\
((res' = st_sec_reserved s /\ Z.of_nat (length (st_sec_arr s)) < st_sec_reserved s) \/
(res' = st_sec_reserved s + kPtrArrayEntriesPerCommit /\ Z.of_nat (length (st_sec_arr s)) = st_sec_reserved s)) /\
ns = true
end.
Lemma sec_alloc_ok : forall U pp cc bb s n ns,
WfP U pp cc bb s -> 1 <= cc -> 0 <= n < MALLOC_MAX -> from_primary n = false ->
atok ns (sec_alloc n s) (sec_alloc_post s n).
Proof.
intros U pp cc bb s n ns W Hcc Hn Hprim.
pose proof (sec_arr_length U pp cc bb s W) as Hal. pose proof (wf_chunks_ev _ _ _ _ _ W) as Hce. pose proof (wf_nev _ _ _ _ _ W) as Hnev.
pose proof (wf_secondary _ _ _ _ _ W) as X. destruct X as [Snd Sac Sal Sres Sral].
unfold sec_alloc. apply atok_bind. apply atok_askz.
{ cbn. exists n. auto. }
intros z Hz. cbn in Hz. cbn [fst snd progz]. destruct Hz as [-> | ->]; cbn [Z.eqb Pos.eqb].
- apply atok_ret. split; reflexivity.
- apply atok_bind. apply atok_get. cbn [fst snd]. apply atok_bind. apply atok_mcheck.
{ apply Z.ltb_lt. unfold kMaxNumChunks, kPtrArrayEntriesPerCommit, EV_MAX in *. lia. }
cbn [fst snd]. apply atok_bind. apply atok_put. cbn [fst snd]. apply atok_bind.
destruct (Z.eqb_spec (Z.of_nat (length (st_sec_arr s))) (st_sec_reserved s)) as [Eidx|Nidx].
+ apply atok_bind. apply atok_askz.
{ cbn -[Z.mul Z.add Z.modulo Z.le kPtrArrayCommit kMaxNumChunks]. unfold kPtrArrayCommit, kMaxNumChunks, kPtrArrayEntriesPerCommit, EV_MAX in *.
destruct Sral as [S1 S2]. splits; try lia.
rewrite Eidx. replace 131072 with (8 * 16384) by reflexivity. rewrite Z.mul_mod_distr_l by lia. rewrite S2. reflexivity. }
intros z2 Hz2. cbn in Hz2. cbn [fst snd]. unfold aGranted. destruct (Z.eqb_spec z2 1) as [->|Nz].
* cbn [progz Z.eqb Pos.eqb]. apply atok_modify. cbn [fst snd]. apply atok_bind. apply atok_modify. cbn [fst snd]. apply atok_ret.
exists (st_sec_reserved s + kPtrArrayEntriesPerCommit). splits; [reflexivity | reflexivity | right; auto | reflexivity].
* replace (progz _ z2) with false. { apply atok_spin. } cbn. destruct Hz2 as [->| ->]; cbn; congruence.
+ apply atok_ret. cbn [fst snd]. apply atok_bind. apply atok_modify. cbn [fst snd]. apply atok_ret.
exists (st_sec_reserved s). splits; [reflexivity | destruct s; reflexivity | left; split; [reflexivity | lia] | reflexivity].
Qed.
Lemma blocks_set_chunks_app : forall s k, blocks (set_chunks (st_chunks s ++ [k]) s) = blocks s ++ (if is_alloc k then [(ck_user k, ck_req k)] else []).
Proof. intros s k. unfold blocks. cbn [st_chunks set_chunks]. rewrite filter_app, map_app. cbn. destruct (is_alloc k); reflexivity. Qed.
Lemma needs_remap_secondary : forall n, 0 <= n -> needs_remap (req_size n) = true -> from_primary n = false.
Proof.
intros n Hn H. unfold needs_remap, kClearShadowMmapThreshold in H. apply Z.leb_le in H.
destruct (from_primary n) eqn:E; [|reflexivity]. exfalso.
pose proof (primary_geometry n Hn E) as (_ & G & K & _). pose proof (req_size_bounds n Hn) as (_ & _ & R).
unfold kMaxSize in K.
assert (req_size n / 8 <= 65536 / 8) by (apply Z.div_le_mono; pose proof (rz_size_bounds n); lia). change (65536/8) with 8192 in *. lia.
Qed.
Lemma secs_ext_app : forall s l f, (forall s, st_secs (f s) = st_secs s ++ l) -> secs_ext s (f s).
Proof.
intros s l f H r sm E. exists sm. rewrite H, nth_error_app1 by (eapply nth_error_lt; exact E). auto.
Qed.
Lemma nrecZ_small : forall U pp cc bb s c, WfP U pp cc bb s -> st_nev s <= EV_MAX -> nrecZ s c + 10248 <= 65536.
Proof.
intros U pp cc bb s c W Hev. pose proof (length_chunk_offs_le s c). pose proof (length_batch_offs_le s c).
pose proof (wf_chunks_ev _ _ _ _ _ W). pose proof (wf_batches_ev _ _ _ _ _ W). pose proof (wf_slack _ _ _ _ _ W).
unfold nrecZ, EV_MAX in *. lia.
Qed.
Lemma sec_arr_small : forall U pp cc bb s, WfP U pp cc bb s -> st_nev s <= EV_MAX -> Z.of_nat (length (st_sec_arr s)) < kPtrArrayEntriesPerCommit.
Proof.
intros U pp cc bb s W Hev. pose proof (sec_arr_length U pp cc bb s W). pose proof (wf_chunks_ev _ _ _ _ _ W). pose proof (wf_slack _ _ _ _ _ W).
unfold kPtrArrayEntriesPerCommit, EV_MAX in *. lia.
Qed.
Lemma cdef_add_prim : forall (s s' : astate) c x n st c',
0 <= c -> 0 <= x < 2 ^ 32 ->
st_regions s' = st_regions s -> st_cache s' = st_cache s -> st_qthread s' = st_qthread s -> st_qglobal s' = st_qglobal s ->
st_chunks s' = st_chunks s ++ [mkChunk (PPrim (region_off c + x)) n st] ->
cdef s' c' = cdef s c' - (if c' =? c then class_size c else 0).
Proof.
intros s s' c x n st c' Hc Hx ER EC EQ1 EQ2 EK. unfold cdef, class_elems, reg, cache.
rewrite (batch_offs_ext s s' c' EQ1 EQ2), ER, EC.
assert (E : chunk_offs s' c' = chunk_offs s c' ++ (if c =? c' then [x] else [])).
{ unfold chunk_offs. rewrite EK, flat_map_app. cbn [flat_map ck_beg app]. rewrite prim_class_region_off by lia. rewrite app_nil_r.
destruct (Z.eqb_spec c c') as [<-|Hne]; [|reflexivity]. replace (region_off c + x - region_off c) with x by lia. reflexivity. }
rewrite E, !length_app, !Nat2Z.inj_add. rewrite (Z.eqb_sym c' c).
destruct (Z.eqb_spec c c') as [->|Hne]; cbn [length]; lia.
Qed.
Theorem malloc_gen : forall U s n tr,
universe_ok U ->
Wf U s -> regime_ok s -> 0 <= n < MALLOC_MAX -> blocks_bytes s + n <= LIVE_MAX -> In tr U ->
atok true (malloc n tr s) (fun ns r => malloc_post U s n ns r /\ (BigInv s -> BigInv (snd r)) /\ mgrow s n (snd r)).
Proof.
intros U s n tr HU W Hreg Hn Hlive Htr.
assert (TREG : st_nev s < EV_MAX \/ (BigP s /\ Z.of_nat (length (st_chunks s)) + 1 <= 2 ^ 23)).
{ destruct Hreg as [Hev | ((_ & HP) & _ & _ & HCH & _)]; [left; exact Hev | right; split; [exact HP | exact HCH]]. }
pose proof (WfP_tick' U s W TREG) as W1. set (s1 := set_nev (st_nev s + 1) s) in *.
assert (PREG1 : forall c, 1 <= c <= 31 -> preg s1 c).
{ intros c Hc. destruct Hreg as [Hev | ((CP & _) & HB & _)]; [left; subst s1; cbn; unfold EV_MAX in *; lia | right].
destruct (HB c Hc) as [HB1 HB2]. split; [exact (CP c Hc) | split; [exact HB1 | exact HB2]]. }
assert (HR1 : forall c, 1 <= c <= 31 -> nrecZ s c + 10248 <= 65536).
{ intros c Hc. destruct Hreg as [Hev | (_ & HB & _)]; [| exact (proj2 (HB c Hc))].
change (nrecZ s c) with (nrecZ s1 c). apply (nrecZ_small U 1 1 1 s1 c W1). subst s1. cbn. unfold EV_MAX in *. lia. }
assert (HSEC1 : Z.of_nat (length (st_sec_arr s1)) < kPtrArrayEntriesPerCommit).
{ destruct Hreg as [Hev | (_ & _ & HS & _)]; [| exact HS]. apply (sec_arr_small U 1 1 1 s1 W1). subst s1. cbn. unfold EV_MAX in *. lia. }
assert (D1 : NoDup (st_depot s1) /\ incl (st_depot s1) U) by exact (wf_depot _ _ _ _ _ W1).
unfold malloc. apply atok_bind. apply atok_tick. cbn [fst snd]. fold s1.
apply atok_bind. apply atok_mcheck; [apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage, MALLOC_MAX in *; lia|]. cbn [fst snd].
apply atok_bind. destruct (from_primary n) eqn:Hprim.
-
pose proof (primary_geometry n ltac:(lia) Hprim) as (Gc & Gsz & Gmax & G32 & Gpos).
apply atok_bind. eapply atok_mono; [|apply (cache_alloc_okx U 1 1 1 s1 (chunk_class n) true W1 ltac:(lia) ltac:(lia) (PREG1 (chunk_class n) ltac:(lia)))].
intros ns2 [o s2] ((W2 & RO2 & Hi2 & Ho) & DEF2 & BIG2). cbn [fst snd] in DEF2, BIG2 |- *. apply atok_ret.
destruct RO2 as (Rck & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rdep & Rii & Rnev).
destruct o as [off|].
+ destruct Ho as (x & -> & Hx32 & Hxa & Hxm & Hxni).
apply atok_bind. eapply atok_mono; [|apply (depot_put_ok U s2 tr ns2); [ | | exact HU | exact Htr]].
2:{ rewrite Rdep. exact (proj1 D1). }
2:{ rewrite Rdep. exact (proj2 D1). }
intros ns3 [[] s3] (d & -> & Hdnd & Hdincl & Hd & ->). cbn [fst snd].
assert (NR : needs_remap (ck_n (mkChunk (PPrim (region_off (chunk_class n) + x)) n CAllocated)) = false).
{ unfold ck_n. cbn [ck_req]. destruct (needs_remap (req_size n)) eqn:E; [|reflexivity]. exfalso.
rewrite (needs_remap_secondary n ltac:(lia) E) in Hprim. discriminate. }
rewrite NR. apply atok_bind. apply atok_ret. cbn [fst snd]. apply atok_bind. apply atok_modify. cbn [fst snd]. apply atok_ret.
pose proof (WfP_set_depot U 0 1 1 s2 d W2 Hdnd Hdincl) as W3.
assert (Hfresh : ~ In (PPrim (region_off (chunk_class n) + x)) (map ck_beg (st_chunks s2))).
{ intros Hin. apply in_map_iff in Hin as (k & Hb & Hk). apply Hxni. unfold class_elems. do 2 (apply in_app_iff; right). apply in_app_iff; left.
unfold chunk_offs. apply in_flat_map. exists k. split; [exact Hk|]. rewrite Hb. rewrite prim_class_region_off by lia. rewrite Z.eqb_refl. left. lia. }
cbn [st_chunks set_depot]. rewrite upd_chunk_fresh by exact Hfresh.
pose proof (WfP_add_prim_chunk U 0 1 1 (set_depot d s2) (region_off (chunk_class n) + x) n W3 ltac:(lia) Hn Hprim) as W4.
rewrite prim_class_region_off in W4 by lia. replace (region_off (chunk_class n) + x - region_off (chunk_class n)) with x in W4 by lia.
cbn [st_chunks set_depot] in W4.
assert (Wfin : Wf U (set_chunks (st_chunks s2 ++ [mkChunk (PPrim (region_off (chunk_class n) + x)) n CAllocated]) (set_depot d s2))).
{ unfold Wf. apply (WfP_weaken U 0 (1 - 1) 1); [|lia|lia|lia]. apply W4; [reflexivity | exact Hx32 | | exact Hfresh |].
-- apply cls_ok_add_ko; [exact (wf_classes _ _ _ _ _ W3 (chunk_class n) ltac:(lia)) | exact Hxni | split; [lia | exact Hxa] | exact Hxm].
-- rewrite (blocks_bytes_set s2 (set_depot d)) by reflexivity. unfold blocks_bytes. rewrite Rck. subst s1. cbn. exact Hlive. }
split; [split; [exact Wfin | split; [|split; [|split; [|split]]]] | split].
* cbn. rewrite Rnev. subst s1. reflexivity.
* intros r sm E. exists sm. cbn. rewrite Rsecs. subst s1. cbn. auto.
* unfold frames. cbn. rewrite Rfs. subst s1. reflexivity.
* lazy [ck_user ck_beg ck_rz ck_req padd].
assert (EB : forall S', st_chunks S' = st_chunks s2 ++ [mkChunk (PPrim (region_off (chunk_class n) + x)) n CAllocated] ->
blocks S' = blocks s ++ [(PPrim (region_off (chunk_class n) + x + rz_size n), n)]).
{ intros S' HS. unfold blocks. rewrite HS, Rck, filter_app, map_app. subst s1. reflexivity. }
rewrite EB by reflexivity. split; [reflexivity|].
intros Hin. apply in_map_iff in Hin as ([p m] & Hp & Hb). cbn [fst] in Hp. subst p.
apply In_blocks in Hb as (k & Hk & Hst & Hu & Hr).
unfold ck_user in Hu. destruct (ck_beg k) as [|boff|rr oo|cc' pp'] eqn:Eb; cbn [padd] in Hu; try discriminate.
injection Hu as Hu.
pose proof (prim_user_inj U 0 0 0 s k boff (chunk_class n) x n W Hk Eb ltac:(lia)) as J.
assert (Hx31 : 0 <= x < 2 ^ 31).
{ pose proof (mapped_user_bound U 0 1 1 s2 (chunk_class n) W2 ltac:(lia)). pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ W2 (chunk_class n) ltac:(lia))).
unfold kUserMapSize, EV_MAX in *. lia. }
specialize (J Hx31 Hxm ltac:(lia) Hprim eq_refl ltac:(lia)).
apply Hfresh. rewrite Rck. replace (st_chunks s1) with (st_chunks s) by (subst s1; reflexivity).
apply in_map_iff. exists k. rewrite Eb, J. auto.
* apply (qtight_alloc_app s _ (mkChunk (PPrim (region_off (chunk_class n) + x)) n CAllocated));
[ cbn [st_chunks set_chunks set_depot]; rewrite Rck; subst s1; reflexivity | reflexivity
| cbn [st_qthread set_chunks set_depot]; rewrite Rqt; subst s1; reflexivity
| cbn [st_qglobal set_chunks set_depot]; rewrite Rqg; subst s1; reflexivity ].
*
intros [CP HB]. cbn [snd]. split.
-- intros c' Hc'.
match goal with |- cdef ?S _ = _ => rewrite (cdef_add_prim s2 S (chunk_class n) x n CAllocated c' ltac:(lia) Hx32 eq_refl eq_refl eq_refl eq_refl eq_refl) end.
rewrite (DEF2 c' Hc'). change (cdef s1 c') with (cdef s c'). rewrite (CP c' Hc'). destruct (c' =? chunk_class n); lia.
-- intros c' Hc'. change (reg (set_chunks ?[a] (set_depot ?[b] s2)) c') with (reg s2 c').
exact (BIG2 (CP (chunk_class n) ltac:(lia)) (HR1 (chunk_class n) ltac:(lia)) HB c' Hc').
*
unfold mgrow, hgrow, sec_hulls. cbn [snd st_chunks st_secs st_qthread st_qglobal set_chunks set_depot]. rewrite Rck, Rsecs, Rqt, Rqg, Hprim.
subst s1. cbn [st_chunks st_secs st_qthread st_qglobal set_nev]. rewrite length_app, crw_app. cbn [length crw fold_right cw ck_beg ck_req].
splits; try reflexivity; lia.
+ subst. apply atok_ret. cbn -[BigInv].
split; [split; [|split; [|split; [|split; [|split]]]] | split].
* unfold Wf. eapply WfP_weaken; [exact W2 | lia | lia | lia].
* rewrite Rnev. subst s1. reflexivity.
* intros r sm E. exists sm. rewrite Rsecs. subst s1. cbn. auto.
* unfold frames. rewrite Rfs. subst s1. reflexivity.
* unfold blocks. rewrite Rck. subst s1. reflexivity.
* apply (qtight_ext s); [rewrite Rck | rewrite Rqt | rewrite Rqg]; subst s1; reflexivity.
*
intros [CP HB]. split.
-- intros c' Hc'. rewrite (DEF2 c' Hc'). change (cdef s1 c') with (cdef s c'). rewrite (CP c' Hc'). destruct (c' =? chunk_class n); lia.
-- exact (BIG2 (CP (chunk_class n) ltac:(lia)) (HR1 (chunk_class n) ltac:(lia)) HB).
* unfold mgrow, hgrow, sec_hulls. rewrite Rck, Rsecs, Rqt, Rqg, Hprim. subst s1. cbn [st_chunks st_secs st_qthread st_qglobal set_nev]. splits; try reflexivity; lia.
-
pose proof (secondary_geometry n ltac:(lia) Hprim) as (S1 & S2 & S3 & S4 & S5 & S6).
eapply atok_mono; [|apply (sec_alloc_ok U 1 1 1 s1 n true W1 ltac:(lia) Hn Hprim)].
intros ns2 [o s2] Ho. cbn [fst snd] in Ho |- *.
destruct o as [p|].
+ destruct Ho as (res' & -> & -> & Hres & ->).
set (r := length (st_secs s1)). set (sm := mkSec (sec_map_size n) (needed_size n) true).
set (s2 := set_sec_arr _ _).
apply atok_bind. eapply atok_mono; [|apply (depot_put_ok U s2 tr true); [exact (proj1 D1) | exact (proj2 D1) | exact HU | exact Htr]].
intros ns3 [[] s3] (d & -> & Hdnd & Hdincl & Hd & ->). cbn [fst snd].
set (k := mkChunk (PSec r kPage) n CAllocated).
assert (Hfresh : ~ In (PSec r kPage) (map ck_beg (st_chunks (set_depot d s2)))).
{ cbn [st_chunks set_depot s2 set_sec_arr set_sec_reserved set_secs]. intros Hin. apply in_map_iff in Hin as (k' & Hb & Hk').
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W1) k' Hk') as [_ CK]. rewrite Hb in CK.
destruct CK as (_ & _ & sm' & Es & _). apply nth_error_lt in Es. subst r. lia. }
assert (TAIL : forall ns4, atok ns4
((modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) k) s0) ;; ret (ck_user k)) (set_depot d s2))
(fun b r0 => atok b (let (_, s') := r0 in IRet (ck_user k, s')) (fun ns r => malloc_post U s n ns r /\ (BigInv s -> BigInv (snd r)) /\ mgrow s n (snd r)))).
{ intros ns4. apply atok_bind. apply atok_modify. cbn [fst snd]. apply atok_ret. apply atok_ret.
rewrite upd_chunk_fresh by exact Hfresh.
pose proof (WfP_add_sec U 1 1 1 s1 n d res' W1 ltac:(lia) Hn Hprim ltac:(subst s1; exact Hlive) Hdnd Hdincl HSEC1 Hres) as W4.
cbn zeta in W4. fold r sm in W4.
assert (ES : set_chunks (st_chunks (set_depot d s2) ++ [k]) (set_depot d s2)
= set_chunks (st_chunks s1 ++ [k]) (set_depot d (set_sec_arr (st_sec_arr s1 ++ [r]) (set_sec_reserved res' (set_secs (st_secs s1 ++ [sm]) s1))))).
{ subst s2 s1. destruct s. reflexivity. }
rewrite ES. split; [split; [|split; [|split; [|split; [|split]]]] | split].
6:{ apply (qtight_alloc_app s _ k); subst s1 k; reflexivity. }
7:{
unfold mgrow, hgrow, sec_hulls. cbn [snd st_chunks st_secs st_qthread st_qglobal set_chunks set_depot set_sec_arr set_sec_reserved set_secs]. rewrite Hprim.
subst s1 k. cbn [st_chunks st_secs st_qthread st_qglobal set_nev]. rewrite !length_app, crw_app, sec_hulls_app1. subst sm. cbn [length crw fold_right cw ck_beg sm_len].
splits; try reflexivity; lia. }
6:{
intros [CP HB]. cbn [snd]. split.
- intros c' Hc'. rewrite <- (CP c' Hc'). apply cdef_ext; [reflexivity|]. unfold class_elems, chunk_offs.
cbn [st_chunks st_regions st_cache st_qthread st_qglobal set_chunks set_depot set_sec_arr set_sec_reserved set_secs].
subst s1 k. cbn [st_chunks set_nev]. rewrite flat_map_app. cbn [flat_map ck_beg app]. rewrite app_nil_r. reflexivity.
- intros c' Hc'. exact (HB c' Hc'). }
- unfold Wf. eapply WfP_weaken; [exact W4 | lia | lia | lia].
- subst s1. cbn. reflexivity.
- intros r0 sm0 E0. exists sm0. subst s1. cbn. rewrite nth_error_app1 by (eapply nth_error_lt; exact E0). auto.
- subst s1. reflexivity.
- assert (EB : forall S', st_chunks S' = st_chunks s1 ++ [k] -> blocks S' = blocks s ++ [(PSec r (kPage + rz_size n), n)]).
{ intros S' HS. unfold blocks. rewrite HS, filter_app, map_app. subst s1 k. reflexivity. }
lazy [ck_user ck_beg padd k ck_rz ck_req]. fold k.
rewrite EB by reflexivity. split; [reflexivity|].
intros Hin. apply in_map_iff in Hin as ([p m] & Hp & Hb). cbn [fst] in Hp. subst p.
apply In_blocks in Hb as (k' & Hk' & _ & Hu & _).
unfold ck_user in Hu. destruct (ck_beg k') as [|boff|rr oo|cc' pp'] eqn:Eb; cbn [padd] in Hu; try discriminate.
injection Hu as <- Hoff. apply Hfresh. cbn [st_chunks set_depot s2 set_sec_arr set_sec_reserved set_secs]. subst s1. cbn [st_chunks set_nev].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W) k' Hk') as [_ CK]. rewrite Eb in CK. destruct CK as (_ & Eoo & _).
apply in_map_iff. exists k'. rewrite Eb, Eoo. auto. }
lazy [ck_n ck_req k]. fold k. destruct (needs_remap (req_size n)) eqn:NR.
* apply atok_bind. apply atok_bind. apply atok_askz.
{ cbn -[Z.mul Z.div Z.add Z.le Z.lt Z.modulo kClearShadowMmapThreshold rz_size req_size sec_map_size needed_size kPage].
unfold needs_remap in NR. apply Z.leb_le in NR.
pose proof (req_size_bounds n ltac:(lia)) as (_ & Q1 & Q2). pose proof (rz_size_bounds n) as [Z1 Z2].
split; [rewrite Z.mul_comm, Z.div_mul by lia; exact NR|].
exists r, (kPage + rz_size n), sm. splits.
- reflexivity.
- subst s2 r s1. cbn [st_secs set_depot set_sec_arr set_sec_reserved set_secs set_nev]. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
- reflexivity.
- unfold kPage. lia.
- subst sm. cbn [sm_len].
pose proof (needed_primary_bounds n ltac:(lia)) as (NP1 & _).
pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)). unfold kPage in *. nia.
- unfold kPage. apply Z.mod_divide; [lia|]. exists (512 + 2 * (rz_size n / 16)). pose proof (Z.div_mod (rz_size n) 16 ltac:(lia)). lia. }
intros z Hz. cbn in Hz. cbn [fst snd]. unfold aGranted. destruct (Z.eqb_spec z 1) as [->|Nz].
-- cbn [progz Z.eqb Pos.eqb]. apply atok_ret. apply TAIL.
-- replace (progz _ z) with false by (cbn; destruct Hz as [->| ->]; cbn; congruence). apply atok_spin.
* apply atok_bind. apply atok_ret. apply TAIL.
+ destruct Ho as [-> ->]. apply atok_ret. cbn -[BigInv].
split; [split; [|split; [|split; [|split; [|split]]]] | split].
* unfold Wf. eapply WfP_weaken; [exact W1 | lia | lia | lia].
* subst s1. reflexivity.
* intros r0 sm0 E0. exists sm0. subst s1. auto.
* subst s1. reflexivity.
* subst s1. reflexivity.
* apply (qtight_ext s); subst s1; reflexivity.
* intros H. exact H.
* unfold mgrow, hgrow, sec_hulls. rewrite Hprim. subst s1. cbn [st_chunks st_secs st_qthread st_qglobal set_nev].
pose proof (sec_map_size_range n Hn) as SMR. pose proof (Z.div_pos (sec_map_size n) 8 ltac:(lia) ltac:(lia)). splits; try reflexivity; lia.
Qed.
Theorem malloc_ok : forall U s n tr,
universe_ok U ->
Wf U s -> aregime s   -> 0 <= n < MALLOC_MAX -> blocks_bytes s + n <= LIVE_MAX -> In tr U ->
atok true (malloc n tr s) (malloc_post U s n).
Proof.
intros U s n tr HU W Hev Hn Hlive Htr.
eapply atok_mono; [|exact (malloc_gen U s n tr HU W (aregime_ok s Hev) Hn Hlive Htr)]. intros b r (H & _). exact H.
Qed.
Theorem malloc_big : forall U s n tr,
universe_ok U ->
Wf U s -> regime_big s -> 0 <= n < MALLOC_MAX -> blocks_bytes s + n <= LIVE_MAX -> In tr U ->
atok true (malloc n tr s) (fun ns r => malloc_post U s n ns r /\ BigInv (snd r) /\ mgrow s n (snd r)).
Proof.
intros U s n tr HU W Hbig Hn Hlive Htr.
eapply atok_mono; [|exact (malloc_gen U s n tr HU W (or_intror Hbig) Hn Hlive Htr)]. intros b r (H1 & H2 & H3). split; [exact H1 | split; [exact (H2 (proj1 Hbig)) | exact H3]].
Qed.
