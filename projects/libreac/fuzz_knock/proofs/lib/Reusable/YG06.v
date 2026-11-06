(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG06.v, with its module paths changed. *)
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Definition upd_reg (c : Z) (r : region) (s : astate) : astate := set_regions (zupd c r (st_regions s)) s.
Definition upd_pc (c : Z) (p : pclass) (s : astate) : astate := set_cache (zupd c p (st_cache s)) s.
Lemma lupd_nth_same {X} : forall (l : list X) i d, (i < length l)%nat -> lupd l i (nth i l d) = l.
Proof. induction l as [|h t IH]; intros [|i] d Hi; cbn in *; try lia; [reflexivity|]. rewrite IH; [reflexivity | lia]. Qed.
Lemma lupd_lupd {X} : forall (l : list X) i v w, lupd (lupd l i v) i w = lupd l i w.
Proof. induction l as [|h t IH]; intros [|i] v w; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma set_regions_st_regions : forall s, set_regions (st_regions s) s = s.
Proof. intros s. destruct s. reflexivity. Qed.
Lemma set_cache_st_cache : forall s, set_cache (st_cache s) s = s.
Proof. intros s. destruct s. reflexivity. Qed.
Lemma upd_reg_same : forall c s, 0 <= c -> (Z.to_nat c < length (st_regions s))%nat -> upd_reg c (reg s c) s = s.
Proof. intros c s Hc Hl. unfold upd_reg, zupd, reg, znth. rewrite lupd_nth_same by exact Hl. apply set_regions_st_regions. Qed.
Lemma upd_reg_upd_reg : forall c r1 r2 s, upd_reg c r2 (upd_reg c r1 s) = upd_reg c r2 s.
Proof. intros. unfold upd_reg, zupd. cbn. rewrite lupd_lupd. reflexivity. Qed.
Lemma reg_upd_reg : forall c r s, 0 <= c -> (Z.to_nat c < length (st_regions s))%nat -> reg (upd_reg c r s) c = r.
Proof. intros. unfold upd_reg. apply reg_upd_same; assumption. Qed.
Lemma reg_upd_reg_other : forall c c' r s, 0 <= c -> 0 <= c' -> c <> c' -> reg (upd_reg c r s) c' = reg s c'.
Proof. intros. unfold upd_reg. apply reg_upd_other; assumption. Qed.
Lemma upd_pc_same : forall c s, 0 <= c -> (Z.to_nat c < length (st_cache s))%nat -> upd_pc c (cache s c) s = s.
Proof. intros c s Hc Hl. unfold upd_pc, zupd, cache, znth. rewrite lupd_nth_same by exact Hl. apply set_cache_st_cache. Qed.
Lemma cache_upd_pc : forall c p s, 0 <= c -> (Z.to_nat c < length (st_cache s))%nat -> cache (upd_pc c p s) c = p.
Proof. intros. unfold upd_pc. apply cache_upd_same; assumption. Qed.
Lemma upd_pc_upd_pc : forall c p1 p2 s, upd_pc c p2 (upd_pc c p1 s) = upd_pc c p2 s.
Proof. intros. unfold upd_pc, zupd. cbn. rewrite lupd_lupd. reflexivity. Qed.
Lemma atok_set_region : forall ns c r s (Q : bool -> unit * astate -> Prop), Q ns (tt, upd_reg c r s) -> atok ns (set_region c r s) Q.
Proof. intros. exact H. Qed.
Lemma atok_set_pc : forall ns c p s (Q : bool -> unit * astate -> Prop), Q ns (tt, upd_pc c p s) -> atok ns (set_pc c p s) Q.
Proof. intros. exact H. Qed.
Lemma WfP_len_regions : forall U pp cc bb s c, WfP U pp cc bb s -> 0 <= c <= 31 -> (Z.to_nat c < length (st_regions s))%nat.
Proof. intros U pp cc bb s c W Hc. rewrite (wf_len_regions _ _ _ _ _ W). lia. Qed.
Lemma WfP_len_cache : forall U pp cc bb s c, WfP U pp cc bb s -> 0 <= c <= 31 -> (Z.to_nat c < length (st_cache s))%nat.
Proof. intros U pp cc bb s c W Hc. rewrite (wf_len_cache _ _ _ _ _ W). lia. Qed.
Lemma round_up_step : forall x base a, 0 < a -> base mod a = 0 -> base < x <= base + a -> round_up x a = base + a.
Proof.
intros x base a Ha Hb Hx. pose proof (round_up_ge x a Ha) as [[R1 R2] R3].
assert (round_up x a <= base + a).
{ apply round_up_le; [lia|lia|]. rewrite Z.add_mod, Hb, Z.mod_same by lia. reflexivity. }
apply Z.mod_divide in R3 as [k Hk]; [|lia]. apply Z.mod_divide in Hb as [m Hm]; [|lia]. subst.
assert (m < k) by nia. assert (k <= m + 1) by nia. nia.
Qed.
Ltac cbnr := cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd].
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Lemma length_chunk_offs_le : forall s c, (length (chunk_offs s c) <= length (st_chunks s))%nat.
Proof.
intros s c. unfold chunk_offs. induction (st_chunks s) as [|k t IH]; cbn [flat_map length]; [lia|].
rewrite length_app. destruct (ck_beg k) as [|off| |]; cbn [length]; try lia. destruct (prim_class off =? c); cbn [length]; lia.
Qed.
Lemma length_batch_offs_le : forall s c, (length (batch_offs s c) <= length (all_batches s))%nat.
Proof. intros s c. unfold batch_offs. destruct (c =? kBatchClass); [rewrite length_map; lia | cbn; lia]. Qed.
Lemma length_cache_le16 : forall c r p (i : bool) ko bo, 1 <= c <= 31 -> cls_ok c r p i ko bo -> Z.of_nat (length (pc_chunks p)) <= 16.
Proof.
intros c r p i ko bo Hc C. pose proof (wr_cache _ _ _ _ _ _ C) as X. pose proof (class_ok c Hc) as (_ & _ & _ & K & _).
destruct i; [destruct X as [_ X]; lia | rewrite X; cbn; lia].
Qed.
Lemma fa_room_populate : forall U pp cc bb s c r',
WfP U pp cc bb s -> 1 <= c <= 31 ->
runs_ok (rg_free r') -> fa_len (rg_free r') <= 8 + 10240 ->
4 <= rg_mapped_fa r' -> rg_mapped_fa r' mod kFreeArrayMapSize = 0 ->
fa_room (rg_alloc_user r') (length (fa_elems (class_size c) (rg_free r') ++ pc_chunks (cache s c) ++ chunk_offs s c ++ batch_offs s c))
(cc + bslack c bb + 2 * (EV_MAX - st_nev s)) (rg_mapped_fa r').
Proof.
intros U pp cc bb s c r' W Hc Hruns Hfl Hpos Hmod. right.
rewrite !length_app, !Nat2Z.inj_add, (fa_elems_length _ _ Hruns).
pose proof (length_chunk_offs_le s c) as L1. pose proof (length_batch_offs_le s c) as L2.
pose proof (wf_classes _ _ _ _ _ W c Hc) as C. unfold wf_class in C. pose proof (length_cache_le16 c _ _ _ _ _ Hc C) as L3.
pose proof (wf_chunks_ev _ _ _ _ _ W) as E1. pose proof (wf_batches_ev _ _ _ _ _ W) as E2. pose proof (wf_nev _ _ _ _ _ W) as E3.
pose proof (wf_slack _ _ _ _ _ W) as E4.
apply Z.mod_divide in Hmod as [q Hq]; [|unfold kFreeArrayMapSize; lia].
pose proof (bslack_le c bb ltac:(lia)) as BS.
unfold kFreeArrayMapSize, EV_MAX in *. nia.
Qed.
Ltac fa_room_keep W c Hc :=
cbnr; eapply fa_room_xfer; [exact (wf_fa_room _ _ _ _ _ W c Hc) | unfold class_elems; cbnr; rewrite ?length_app; lia | cbnr; lia].
Lemma hole_ok_del : forall r off l, Forall (hole_ok r) l -> Forall (hole_ok r) (del_hole off l).
Proof. intros r off l H. unfold del_hole. apply Forall_forall. intros h Hh. apply filter_In in Hh as [Hh _]. exact (proj1 (Forall_forall _ _) H h Hh). Qed.
Lemma NoDup_filter {X} : forall (f : X -> bool) l, NoDup l -> NoDup (filter f l).
Proof.
intros f l H. induction H as [|x t Hni Hnd IH]; cbn; [constructor|].
destruct (f x); [constructor; [intros Hin; apply filter_In in Hin as [Hin _]; exact (Hni Hin) | exact IH] | exact IH].
Qed.
Lemma NoDup_del_hole : forall off l, NoDup l -> NoDup (del_hole off l).
Proof. intros. unfold del_hole. apply NoDup_filter. assumption. Qed.
Lemma cls_ok_map_user : forall c r p i ko bo,
cls_ok c r p i ko bo -> rg_mapped_user r - rg_alloc_user r < kMaxSize ->
rg_mapped_user r + kUserMapSize <= kUserMapSize * EV_MAX ->
cls_ok c (mkRegion (rg_mapped_user r + kUserMapSize) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r)
(del_hole (rg_mapped_user r) (rg_holes r))) p i ko bo.
Proof.
intros c r p i ko bo C Hcv Hroom.
pose proof (wr_alloc _ _ _ _ _ _ C). pose proof (wr_mapped_al _ _ _ _ _ _ C). pose proof (wr_fa _ _ _ _ _ _ C).
pose proof (wr_fa_bound _ _ _ _ _ _ C). pose proof (wr_holes _ _ _ _ _ _ C) as [Hh Hnd].
constructor; cbnr; try (exact (wr_alloc_al _ _ _ _ _ _ C)); try (exact (wr_fa_len _ _ _ _ _ _ C)); try (exact (wr_fa_bound _ _ _ _ _ _ C));
try (exact (wr_runs _ _ _ _ _ _ C)); try (exact (wr_nodup _ _ _ _ _ _ C)); try (exact (wr_elems _ _ _ _ _ _ C)); try (exact (wr_cache _ _ _ _ _ _ C)).
- unfold kUserMapSize in *. lia.
- unfold kUserMapSize, kMaxSize in *. lia.
- rewrite Z.add_mod, Z.mod_same by (unfold kUserMapSize; lia). rewrite H0. reflexivity.
- assumption.
- split; [|apply NoDup_del_hole; exact Hnd]. apply hole_ok_del. exact Hh.
- exact Hroom.
Qed.
Lemma cls_ok_map_fa : forall c r p i ko bo fa',
cls_ok c r p i ko bo ->
rg_mapped_fa r <= fa' -> fa' mod kFreeArrayMapSize = 0 -> fa' <= kFreeArrayMax ->
cls_ok c (mkRegion (rg_mapped_user r) (rg_alloc_user r) fa' (rg_free r)
(del_hole (kFreeArrayOffset + rg_mapped_fa r) (rg_holes r))) p i ko bo.
Proof.
intros c r p i ko bo fa' C H1 H2 H3. pose proof (wr_holes _ _ _ _ _ _ C) as [Hh Hnd]. pose proof (wr_fa _ _ _ _ _ _ C).
pose proof (wr_fa_len _ _ _ _ _ _ C).
constructor; cbnr; try (exact (wr_alloc _ _ _ _ _ _ C)); try (exact (wr_carved _ _ _ _ _ _ C)); try (exact (wr_mapped_al _ _ _ _ _ _ C));
try (exact (wr_alloc_al _ _ _ _ _ _ C)); try (exact (wr_runs _ _ _ _ _ _ C)); try (exact (wr_nodup _ _ _ _ _ _ C));
try (exact (wr_elems _ _ _ _ _ _ C)); try (exact (wr_cache _ _ _ _ _ _ C)); try (exact (wr_mapped_bound _ _ _ _ _ _ C)); try lia.
split; [|apply NoDup_del_hole; exact Hnd]. apply hole_ok_del. exact Hh.
Qed.
Lemma mapped_user_bound_small : forall U pp cc bb s c, WfP U pp cc bb s -> 1 <= c <= 31 -> st_nev s <= EV_MAX ->
rg_mapped_user (reg s c) + kUserMapSize * pp <= kUserMapSize * EV_MAX.
Proof.
intros U pp cc bb s c W Hc Hev. pose proof (mapped_le_prim U pp cc bb s c W ltac:(lia)) as [_ H].
pose proof (wf_prim_ev _ _ _ _ _ W). pose proof (wf_nev _ _ _ _ _ W). pose proof (wf_slack _ _ _ _ _ W).
unfold kUserMapSize, EV_MAX in *. nia.
Qed.
Lemma mapped_user_bound : forall U pp cc bb s c, WfP U pp cc bb s -> 1 <= c <= 31 ->
rg_mapped_user (reg s c) + kUserMapSize * 0 <= kUserMapSize * EV_MAX.
Proof.
intros U pp cc bb s c W Hc. pose proof (wr_mapped_bound _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c Hc)). lia.
Qed.
Lemma regime_cap_keep : forall U pp cc bb s c r', WfP U pp cc bb s -> 1 <= c <= 31 ->
rg_alloc_user r' = rg_alloc_user (reg s c) -> rg_mapped_fa (reg s c) <= rg_mapped_fa r' ->
st_nev s <= EV_MAX \/ rg_alloc_user r' = 0 \/ 4 * (rg_alloc_user r' / class_size c) <= rg_mapped_fa r'.
Proof.
intros U pp cc bb s c r' W Hc EA MF. destruct (wf_regime _ _ _ _ _ W) as [Hs|[HP _]]; [left; exact Hs | right].
rewrite EA. destruct (HP c Hc) as [Z0|HR]; [left; exact Z0 | right; lia].
Qed.
Definition ensure_post (U : list (list Z)) (pp cc bb : Z) (s : astate) (c need : Z) (sof : bool) (ns : bool) (res : bool * astate) : Prop :=
let (ok, s') := res in
exists r', s' = upd_reg c r' s /\ WfP U pp cc bb s' /\
rg_mapped_user r' = rg_mapped_user (reg s c) /\ rg_alloc_user r' = rg_alloc_user (reg s c) /\
rg_free r' = rg_free (reg s c) /\ rg_mapped_fa (reg s c) <= rg_mapped_fa r' /\
(ok = true -> 4 * need <= rg_mapped_fa r') /\ (ok = false -> ns = false /\ sof = false).
Lemma ensure_free_array_ok : forall U pp cc bb s c need sof ns,
WfP U pp cc bb s -> 1 <= c <= 31 ->
fa_len (rg_free (reg s c)) <= need ->
4 * need <= rg_mapped_fa (reg s c) + kFreeArrayMapSize ->
4 * need <= kFreeArrayMax ->
atok ns (ensure_free_array c need sof s) (ensure_post U pp cc bb s c need sof).
Proof.
intros U pp cc bb s c need sof ns W Hc Hlen Hneed Hneed2.
pose proof (wf_classes _ _ _ _ _ W c Hc) as C. unfold wf_class in C.
pose proof (wr_fa _ _ _ _ _ _ C) as [F0 Fal]. pose proof (wr_fa_bound _ _ _ _ _ _ C) as Fb.
pose proof (mapped_user_bound U pp cc bb s c W Hc) as MB. pose proof (wf_slack _ _ _ _ _ W) as SL.
assert (HL : (Z.to_nat c < length (st_regions s))%nat) by (eapply WfP_len_regions; [exact W | lia]).
assert (ES : upd_reg c (reg s c) s = s) by (apply upd_reg_same; [lia | exact HL]).
assert (D8 : forall a b, a <= b -> a / 8 <= b / 8) by (intros; apply Z.div_le_mono; lia).
unfold ensure_free_array. apply atok_bind. apply atok_get_region. cbn [fst snd].
destruct (Z.leb_spec (4 * need) (rg_mapped_fa (reg s c))) as [Hle|Hgt].
- apply atok_ret. exists (reg s c). rewrite ES. splits; auto; try lia.
- set (fa := rg_mapped_fa (reg s c)) in *.
assert (RU : round_up (4 * need) kFreeArrayMapSize = fa + kFreeArrayMapSize).
{ apply round_up_step; [unfold kFreeArrayMapSize; lia | exact Fal | lia]. }
assert (B29 : fa + kFreeArrayMapSize <= kFreeArrayMax).
{ apply Z.mod_divide in Fal as [q Hq]; [|unfold kFreeArrayMapSize; lia]. unfold kFreeArrayMax, kFreeArrayMapSize in *. nia. }
apply atok_bind. apply atok_mcheck; [apply Z.leb_le; rewrite RU; exact B29|].
cbn [fst snd]. apply atok_bind. apply atok_askz.
{ cbn [areq_ok]. rewrite RU. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Fal|]. split; [lia|].
pose proof (wr_holes _ _ _ _ _ _ C) as [Hh _]. eapply Forall_impl; [|exact Hh]. intros h Hho. destruct Hho.   }
intros z Hz. cbn [fst snd].
assert (K : forall s1 r1, s1 = upd_reg c r1 s -> WfP U pp cc bb s1 ->
rg_mapped_user r1 = rg_mapped_user (reg s c) -> rg_alloc_user r1 = rg_alloc_user (reg s c) ->
rg_free r1 = rg_free (reg s c) -> rg_mapped_fa r1 = fa -> aGranted z = false ->
atok (z =? 1) ((if sof then spin 7 else ret false) s1) (ensure_post U pp cc bb s c need sof)).
{ intros s1 r1 -> W1 E1 E2 E3 E4 Eg'. unfold aGranted in Eg'. rewrite Eg'.
destruct sof; [apply atok_spin|]. apply atok_ret. exists r1. splits; auto; try lia. }
cbn [progz]. destruct (aGranted z) eqn:Eg.
+ apply atok_bind. apply atok_set_region. cbn [fst snd]. apply atok_ret.
eexists. split; [reflexivity|]. rewrite RU.
split; [| cbnr; splits; try reflexivity; try lia; intros; discriminate].
eapply WfP_set_region; [exact W | exact Hc | | lia | pose proof (wf_prim_ev _ _ _ _ _ W); cbnr; lia | unfold kFreeArrayMapSize in *; fa_room_keep W c Hc
| apply (regime_cap_keep U pp cc bb s c _ W Hc); cbnr; [reflexivity | unfold kFreeArrayMapSize in *; lia]].
apply cls_ok_map_fa; [exact C | lia | | ].
* rewrite Z.add_mod, Fal, Z.mod_same by (unfold kFreeArrayMapSize; lia). reflexivity.
* exact B29.
+ apply atok_bind. replace (aDestroyed z) with false by (unfold aDestroyed; destruct Hz as [-> | ->]; reflexivity).
apply atok_ret. cbn [fst snd]. eapply (K s (reg s c)); try reflexivity; [symmetry; exact ES | exact W].
Qed.
Lemma WfP_weaken : forall U pp cc bb pp' cc' bb' s,
WfP U pp cc bb s -> 0 <= pp' <= pp -> 0 <= cc' <= cc -> 0 <= bb' <= bb -> WfP U pp' cc' bb' s.
Proof.
intros U pp cc bb pp' cc' bb' s W H1 H2 H3. wf_fields W. constructor; wf_easy; unfold kUserMapSize in *; try lia.
intros c Hc. pose proof (bslack_mono c bb bb' ltac:(lia)). eapply fa_room_xfer; [exact (Xroom c Hc) | lia | apply Z.le_refl].
Qed.
Lemma prim_class_region_off : forall c x, 0 <= c -> 0 <= x < 2 ^ 32 -> prim_class (region_off c + x) = c.
Proof.
intros c x Hc Hx. unfold prim_class, region_off. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma cls_ok_populate : forall c r p i ko bo,
cls_ok c r p i ko bo -> 0 < class_size c ->
let cnt := (rg_mapped_user r - rg_alloc_user r) / class_size c in
1 <= cnt -> 4 * (fa_len (rg_free r) + cnt) <= rg_mapped_fa r ->
cls_ok c (mkRegion (rg_mapped_user r) (rg_alloc_user r + cnt * class_size c) (rg_mapped_fa r)
(FRun (rg_alloc_user r) cnt :: rg_free r) (rg_holes r)) p i ko bo.
Proof.
intros c r p i ko bo C Hsz cnt Hcnt Hfa.
pose proof (wr_alloc _ _ _ _ _ _ C) as A. pose proof (wr_alloc_al _ _ _ _ _ _ C) as Aal.
pose proof (wr_nodup _ _ _ _ _ _ C) as ND. pose proof (wr_elems _ _ _ _ _ _ C) as EL. pose proof (wr_holes _ _ _ _ _ _ C) as [Hh Hnd].
assert (Hdiv : cnt * class_size c <= rg_mapped_user r - rg_alloc_user r).
{ subst cnt. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
assert (Hrem : rg_mapped_user r - rg_alloc_user r - cnt * class_size c < class_size c).
{ subst cnt. pose proof (Z.mod_pos_bound (rg_mapped_user r - rg_alloc_user r) (class_size c) Hsz).
pose proof (Z.div_mod (rg_mapped_user r - rg_alloc_user r) (class_size c) ltac:(lia)). nia. }
pose proof (class_ok c) as CO.
constructor; cbnr; try (exact (wr_mapped_al _ _ _ _ _ _ C)); try (exact (wr_fa _ _ _ _ _ _ C)); try (exact (wr_fa_bound _ _ _ _ _ _ C));
try (exact (wr_cache _ _ _ _ _ _ C)); try (exact (wr_mapped_bound _ _ _ _ _ _ C)).
- nia.
- unfold kUserMapSize, kMaxSize in *. pose proof (wr_carved _ _ _ _ _ _ C). unfold kUserMapSize, kMaxSize in *. nia.
- rewrite Z.add_mod, Aal, Z_mod_mult by lia. reflexivity.
- cbn [fa_len]. lia.
- constructor; [lia | exact (wr_runs _ _ _ _ _ _ C)].
- rewrite fa_elems_cons_run, <- app_assoc. apply NoDup_app_iff. split; [apply run_elems_NoDup; lia|]. split; [exact ND|].
intros x Hx Hy. apply In_run_elems in Hx as (j & Hj & ->).
pose proof (proj1 (Forall_forall _ _) EL _ Hy) as [B _]. nia.
- rewrite fa_elems_cons_run, <- app_assoc. apply Forall_app. split.
+ apply Forall_forall. intros x Hx. apply In_run_elems in Hx as (j & Hj & ->). split; [nia|].
rewrite Z.add_mod, Aal, Z_mod_mult by lia. reflexivity.
+ eapply Forall_impl; [|exact EL]. cbn beta. intros x [B M]. split; [nia | exact M].
- split; [|exact Hnd]. eapply Forall_impl; [|exact Hh]. intros h Hho. unfold hole_ok in *. cbnr. exact Hho.
Qed.
Lemma cls_ok_add_ko : forall c r p i ko bo x,
cls_ok c r p i ko bo ->
~ In x (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo) ->
0 <= x < rg_alloc_user r -> x mod class_size c = 0 ->
cls_ok c r p i (ko ++ [x]) bo.
Proof.
intros c r p i ko bo x C Hni Hx Hm.
assert (HP : Permutation (x :: fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo)
(fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ (ko ++ [x]) ++ bo)).
{ rewrite <- (app_assoc ko [x] bo). cbn [app]. rewrite !app_assoc.
rewrite (app_assoc (fa_elems (class_size c) (rg_free r) ++ pc_chunks p) ko (x :: bo)) || idtac.
replace (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ x :: bo)
with ((fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko) ++ x :: bo) by (rewrite <- !app_assoc; reflexivity).
replace (x :: fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo)
with (x :: (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko) ++ bo) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_middle. }
constructor; try (exact (wr_alloc _ _ _ _ _ _ C)); try (exact (wr_carved _ _ _ _ _ _ C)); try (exact (wr_mapped_al _ _ _ _ _ _ C)); try (exact (wr_alloc_al _ _ _ _ _ _ C));
try (exact (wr_fa _ _ _ _ _ _ C)); try (exact (wr_fa_bound _ _ _ _ _ _ C)); try (exact (wr_fa_len _ _ _ _ _ _ C));
try (exact (wr_runs _ _ _ _ _ _ C)); try (exact (wr_holes _ _ _ _ _ _ C)); try (exact (wr_cache _ _ _ _ _ _ C)); try (exact (wr_mapped_bound _ _ _ _ _ _ C)).
- eapply Permutation_NoDup; [exact HP|]. constructor; [exact Hni | exact (wr_nodup _ _ _ _ _ _ C)].
- eapply Forall_Permutation; [exact HP|]. constructor; [split; [exact Hx | exact Hm] | exact (wr_elems _ _ _ _ _ _ C)].
Qed.
Lemma fa_len_bound : forall c r p i ko bo,
cls_ok c r p i ko bo -> 0 < class_size c -> class_size c * fa_len (rg_free r) <= rg_alloc_user r.
Proof.
intros c r p i ko bo C Hsz.
pose proof (wr_nodup _ _ _ _ _ _ C) as ND. pose proof (wr_elems _ _ _ _ _ _ C) as EL. pose proof (wr_runs _ _ _ _ _ _ C) as R.
apply NoDup_app_iff in ND as (ND & _ & _). apply Forall_app in EL as [EL _].
rewrite <- (fa_elems_length (class_size c)) by exact R.
apply multiples_bound; [exact Hsz | pose proof (wr_alloc _ _ _ _ _ _ C); lia | exact (wr_alloc_al _ _ _ _ _ _ C) | exact ND | exact EL].
Qed.
Definition map_post (U : list (list Z)) (pp cc bb : Z) (s : astate) (c need : Z) (ns : bool) (res : bool * astate) : Prop :=
let (ok, s') := res in
exists r', s' = upd_reg c r' s /\ WfP U (pp - 1) cc bb s' /\
rg_alloc_user r' = rg_alloc_user (reg s c) /\ rg_free r' = rg_free (reg s c) /\ rg_mapped_fa r' = rg_mapped_fa (reg s c) /\
rg_mapped_user (reg s c) <= rg_mapped_user r' <= rg_mapped_user (reg s c) + kUserMapSize /\
(ok = true -> rg_alloc_user (reg s c) + need * class_size c <= rg_mapped_user r') /\ (ok = false -> ns = false).
Lemma map_more_user_ok : forall U pp cc bb s c need ns,
WfP U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp ->
0 < need * class_size c <= kMaxSize ->
rg_mapped_user (reg s c) + kUserMapSize <= kUserMapSize * EV_MAX ->
atok ns (map_more_user c need s) (map_post U pp cc bb s c need).
Proof.
intros U pp cc bb s c need ns W Hc Hpp Hneed Hroom.
pose proof (wf_classes _ _ _ _ _ W c Hc) as C. unfold wf_class in C.
pose proof (wr_alloc _ _ _ _ _ _ C) as A. pose proof (wr_mapped_al _ _ _ _ _ _ C) as Mal.
pose proof Hroom as MB. pose proof (wf_slack _ _ _ _ _ W) as SL.
assert (HL : (Z.to_nat c < length (st_regions s))%nat) by (eapply WfP_len_regions; [exact W | lia]).
assert (ES : upd_reg c (reg s c) s = s) by (apply upd_reg_same; [lia | exact HL]).
assert (Wk : WfP U (pp - 1) cc bb s) by (eapply WfP_weaken; [exact W | lia | lia | lia]).
unfold map_more_user. apply atok_bind. apply atok_get_region. cbn [fst snd].
set (mapped := rg_mapped_user (reg s c)) in *. set (alloc := rg_alloc_user (reg s c)) in *.
destruct (Z.ltb_spec mapped (alloc + need * class_size c)) as [Hlt|Hge].
- assert (RU : round_up (alloc + need * class_size c - mapped) kUserMapSize = kUserMapSize).
{ rewrite <- (Z.add_0_l kUserMapSize) at 2. apply round_up_step; [unfold kUserMapSize; lia | reflexivity | unfold kUserMapSize, kMaxSize in *; lia]. }
rewrite RU. apply atok_bind. apply atok_mcheck.
{ apply Z.leb_le. unfold kFreeArrayOffset, kUserMapSize, EV_MAX in *. lia. }
cbn [fst snd]. apply atok_bind. apply atok_askz.
{ cbn [areq_ok]. splits; try reflexivity; try lia; try exact Mal; try (unfold kFreeArrayOffset, kUserMapSize, EV_MAX in *; lia).
pose proof (wr_holes _ _ _ _ _ _ C) as [Hh _]. eapply Forall_impl; [|exact Hh]. intros h Hho. destruct Hho.   }
intros z Hz. cbn [fst snd progz]. unfold aGranted. destruct (Z.eqb_spec z 1) as [->|Hz1].
+ apply atok_bind. apply atok_set_region. cbn [fst snd]. apply atok_ret.
eexists. split; [reflexivity|]. split; [| cbnr; splits; try reflexivity; unfold kUserMapSize, kMaxSize in *; try lia; intros; discriminate].
eapply WfP_set_region; [exact W | exact Hc | apply cls_ok_map_user; [exact C | unfold kMaxSize in *; lia | exact MB] | lia | pose proof (wf_prim_ev _ _ _ _ _ W); cbnr; unfold kUserMapSize in *; lia | fa_room_keep W c Hc
| apply (regime_cap_keep U pp cc bb s c _ W Hc); cbnr; [reflexivity | lia]].
+ apply atok_bind. replace (aDestroyed z) with false by (unfold aDestroyed; destruct Hz as [-> | ->]; [reflexivity | exfalso; apply Hz1; reflexivity]).
apply atok_ret. cbn [fst snd]. apply atok_ret. exists (reg s c). rewrite ES.
splits; try reflexivity; try assumption; unfold kUserMapSize, kMaxSize in *; try lia.
- apply atok_ret. exists (reg s c). rewrite ES. splits; try reflexivity; try assumption; unfold kUserMapSize, kMaxSize in *; try lia.
Qed.
Ltac show := match goal with |- ?g => idtac g end.
Definition populate_post (U : list (list Z)) (pp cc bb : Z) (s : astate) (c need : Z) (ns : bool) (res : bool * astate) : Prop :=
let (ok, s') := res in
exists r', s' = upd_reg c r' s /\ WfP U (pp - 1) cc bb s' /\
fa_len (rg_free (reg s c)) <= fa_len (rg_free r') /\
(ok = true -> fa_len (rg_free (reg s c)) + need <= fa_len (rg_free r')) /\ (ok = false -> ns = false).
Definition carve_x (s : astate) (c : Z) (r' : region) : Prop :=
rg_alloc_user r' - rg_alloc_user (reg s c) = class_size c * (fa_len (rg_free r') - fa_len (rg_free (reg s c))) /\
rg_mapped_fa (reg s c) <= rg_mapped_fa r' /\
fa_len (rg_free (reg s c)) <= fa_len (rg_free r') /\
(fa_len (rg_free r') = fa_len (rg_free (reg s c)) \/ fa_len (rg_free r') <= 8 + 10240).
Definition populate_postx (U : list (list Z)) (pp cc bb : Z) (s : astate) (c need : Z) (ns : bool) (res : bool * astate) : Prop :=
let (ok, s') := res in
exists r', s' = upd_reg c r' s /\ WfP U (pp - 1) cc bb s' /\
fa_len (rg_free (reg s c)) <= fa_len (rg_free r') /\
(ok = true -> fa_len (rg_free (reg s c)) + need <= fa_len (rg_free r')) /\ (ok = false -> ns = false) /\
carve_x s c r'.
Lemma populate_okx : forall U pp cc bb s c need ns,
WfP U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> 1 <= need ->
need * class_size c <= kMaxSize -> fa_len (rg_free (reg s c)) <= 8 ->
rg_mapped_user (reg s c) + kUserMapSize <= kUserMapSize * EV_MAX ->
(st_nev s <= EV_MAX \/ rg_alloc_user (reg s c) <= class_size c * (65536 - 10240)) ->
atok ns (populate c need s) (populate_postx U pp cc bb s c need).
Proof.
intros U pp cc bb s c need ns W Hc Hpp Hneed Hnsz Hfl8 Hroom Hcarve.
pose proof (class_ok c Hc) as (Ksz & K32 & Kmax & _).
assert (K32' : 32 <= class_size c). { pose proof K32 as K. apply Z.mod_divide in K as [k Hk]; [nia | lia]. }
assert (HL : (Z.to_nat c < length (st_regions s))%nat) by (eapply WfP_len_regions; [exact W | lia]).
unfold populate. apply atok_bind.
eapply atok_mono; [|apply (map_more_user_ok U pp cc bb s c need ns W Hc Hpp ltac:(nia) Hroom)].
intros ns1 [ok s1] (r1 & -> & W1 & A1 & F1 & M1 & MM & OK1 & NS1). cbn [fst snd].
destruct ok; cbn [negb].
2:{ apply atok_ret. exists r1. splits; [reflexivity | exact W1 | rewrite F1; lia | intros; discriminate | exact NS1 |].
unfold carve_x. rewrite A1, F1, M1. pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c Hc))). splits; lia. }
specialize (OK1 eq_refl).
apply atok_bind. apply atok_get_region. rewrite reg_upd_reg by (lia || exact HL). cbn [fst snd].
pose proof (wf_classes _ _ _ _ _ W1 c Hc) as C1. unfold wf_class in C1. rewrite reg_upd_reg in C1 by (lia || exact HL).
set (cnt := (rg_mapped_user r1 - rg_alloc_user r1) / class_size c).
assert (Hcnt1 : need <= cnt). { subst cnt. apply Z.div_le_lower_bound; [lia|]. rewrite A1. nia. }
assert (Hcnt2 : cnt * class_size c <= rg_mapped_user r1 - rg_alloc_user r1). { subst cnt. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
assert (Hcnt4 : cnt <= 10240).
{ pose proof (wr_carved _ _ _ _ _ _ C1) as CV. unfold kUserMapSize, kMaxSize in *.
assert (cnt <= (262144 + 65536) / class_size c) by (subst cnt; apply Z.div_le_mono; lia).
assert ((262144 + 65536) / class_size c <= (262144 + 65536) / 32) by (apply Z.div_le_compat_l; lia).
change ((262144 + 65536) / 32) with 10240 in H0. lia. }
assert (Hcnt3 : 4 * cnt <= kUserMapSize - 4) by (unfold kUserMapSize; lia).
pose proof (fa_len_bound _ _ _ _ _ _ C1 Ksz) as FB. rewrite F1 in FB. rewrite A1 in FB. rewrite ?F1, ?A1.
apply atok_bind.
eapply atok_mono; [|apply (ensure_free_array_ok U (pp - 1) cc bb (upd_reg c r1 s) c (fa_len (rg_free (reg s c)) + cnt) false ns1 W1 Hc)].
2:{ rewrite reg_upd_reg by (lia || exact HL). rewrite F1. lia. }
2:{ rewrite reg_upd_reg by (lia || exact HL). pose proof (wr_fa_len _ _ _ _ _ _ C1) as FL. rewrite F1 in FL. unfold kUserMapSize, kFreeArrayMapSize in *. lia. }
2:{ assert (32 * fa_len (rg_free (reg s c)) <= class_size c * fa_len (rg_free (reg s c))) by (apply Z.mul_le_mono_nonneg_r; [|lia]; pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ C1)); rewrite F1 in *; lia).
assert (32 * cnt <= cnt * class_size c) by nia.
pose proof (mapped_user_bound U (pp - 1) cc bb (upd_reg c r1 s) c W1 Hc) as MB. rewrite reg_upd_reg in MB by (lia || exact HL).
pose proof (wf_slack _ _ _ _ _ W1). pose proof (wr_alloc _ _ _ _ _ _ C1).
unfold kFreeArrayMax, kUserMapSize, EV_MAX in *. lia. }
intros ns2 [ok2 s2] (r2 & -> & W2 & M2 & A2 & F2 & FA2 & OK2 & NS2). cbn [fst snd]. rewrite upd_reg_upd_reg in *.
rewrite reg_upd_reg in M2, A2, F2, FA2 by (lia || exact HL).
destruct ok2; cbn [negb].
2:{ apply atok_ret. exists r2. splits; [reflexivity | exact W2 | rewrite F2, F1; lia | intros; discriminate | intros E; exact (proj1 (NS2 E)) |].
unfold carve_x. rewrite A2, A1, F2, F1, <- M1. splits; lia. }
specialize (OK2 eq_refl).
assert (HL2 : (Z.to_nat c < length (st_regions (upd_reg c r2 s)))%nat) by (unfold upd_reg; cbn; rewrite zupd_length; exact HL).
apply atok_bind. apply atok_get_region. rewrite reg_upd_reg by (lia || exact HL2). cbn [fst snd].
apply atok_bind. apply atok_set_region. cbn [fst snd]. apply atok_ret.
eexists. rewrite upd_reg_upd_reg. split; [reflexivity|].
pose proof (wf_classes _ _ _ _ _ W2 c Hc) as C2. unfold wf_class in C2. rewrite reg_upd_reg in C2 by (lia || exact HL2).
assert (Ecnt : (rg_mapped_user r2 - rg_alloc_user r2) / class_size c = cnt) by (subst cnt; rewrite M2, A2; reflexivity).
split; [| unfold carve_x; cbnr; rewrite F2, F1; cbn [fa_len]; split; [lia | split; [intros _; lia | split; [intros; discriminate | rewrite A2, A1, <- M1; splits; lia]]]].
match goal with |- WfP _ _ _ _ (upd_reg c ?r3 s) =>
rewrite <- (upd_reg_upd_reg c r2 r3 s); unfold upd_reg at 1 end.
eapply (WfP_set_region U (pp - 1) cc bb (upd_reg c r2 s) c); [exact W2 | exact Hc | | lia | | | ].
4:{
change (st_nev (upd_reg c r2 s)) with (st_nev s). destruct Hcarve as [Hs|Hcv]; [left; exact Hs | right; right]. cbnr.
pose proof (wr_alloc_al _ _ _ _ _ _ C2) as AL2. pose proof (wr_fa _ _ _ _ _ _ C2) as [F0 Fal]. pose proof (wr_alloc _ _ _ _ _ _ C2) as [A0 _].
apply Z.mod_divide in AL2 as [q Hq]; [|lia]. apply Z.mod_divide in Fal as [qf Hqf]; [|unfold kFreeArrayMapSize; lia].
rewrite Hq, <- Z.mul_add_distr_r, Z.div_mul by lia. rewrite A2, A1 in Hq.
assert (q <= 65536 - 10240) by nia. pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ C1)) as FL0. rewrite F1 in FL0.
unfold kFreeArrayMapSize in *. nia. }
- pose proof (cls_ok_populate c r2 _ _ _ _ C2 Ksz) as CP. cbn beta in CP. rewrite Ecnt in CP.
apply CP; [lia|]. rewrite F2, F1. lia.
- rewrite reg_upd_reg by (lia || exact HL2). cbnr. pose proof (wf_prim_ev _ _ _ _ _ W2) as PE. unfold kUserMapSize in *. lia.
-
apply (fa_room_populate U (pp - 1) cc bb (upd_reg c r2 s) c _ W2 Hc); cbnr.
+ constructor; [lia | exact (wr_runs _ _ _ _ _ _ C2)].
+ cbn [fa_len]. rewrite F2, F1. lia.
+ pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ C1)) as FL0. rewrite F1 in FL0. lia.
+ exact (proj2 (wr_fa _ _ _ _ _ _ C2)).
Qed.
Lemma populate_ok : forall U pp cc bb s c need ns,
WfP U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> 1 <= need ->
need * class_size c <= kMaxSize -> fa_len (rg_free (reg s c)) <= 8 ->
rg_mapped_user (reg s c) + kUserMapSize <= kUserMapSize * EV_MAX ->
(st_nev s <= EV_MAX \/ rg_alloc_user (reg s c) <= class_size c * (65536 - 10240)) ->
atok ns (populate c need s) (populate_post U pp cc bb s c need).
Proof.
intros U pp cc bb s c need ns W Hc Hpp Hneed Hnsz Hfl8 Hroom Hcarve.
eapply atok_mono; [|exact (populate_okx U pp cc bb s c need ns W Hc Hpp Hneed Hnsz Hfl8 Hroom Hcarve)].
intros b [ok s'] (r' & E & W' & F & OK & NS & _). exists r'. auto.
Qed.
Lemma fa_pop_n_some : forall fuel sz n l acc,
runs_ok l -> 0 <= n <= fa_len l -> n < Z.of_nat fuel ->
exists tops rest, fa_pop_n fuel sz n l acc = Some (tops, rest).
Proof.
induction fuel as [|fuel IH]; intros sz n l acc Hr Hn Hf; cbn [fa_pop_n].
- cbn in Hf. lia.
- destruct (Z.leb_spec n 0) as [Hle|Hgt]; [eauto|].
destruct (fa_pop sz l) as [[off l']|] eqn:Ep.
+ destruct (fa_pop_spec sz l off l' Hr Ep) as (E1 & E2 & R'). apply IH; [exact R' | lia | rewrite Nat2Z.inj_succ in Hf; lia].
+ pose proof (fa_pop_None sz l Hr Ep). lia.
Qed.
Definition gfa_post (U : list (list Z)) (pp cc bb : Z) (s : astate) (c n : Z) (ns : bool) (res : option (list Z) * astate) : Prop :=
let (o, s') := res in
match o with
| None => exists r', s' = upd_reg c r' s /\ WfP U (pp - 1) cc bb s' /\ ns = false
| Some tops => exists r2 rest,
WfP U (pp - 1) cc bb (upd_reg c r2 s) /\
s' = upd_reg c (mkRegion (rg_mapped_user r2) (rg_alloc_user r2) (rg_mapped_fa r2) rest (rg_holes r2)) s /\
runs_ok rest /\ fa_elems (class_size c) (rg_free r2) = tops ++ fa_elems (class_size c) rest /\
Z.of_nat (length tops) = n /\ fa_len rest = fa_len (rg_free r2) - n
end.
Definition gfa_postx (U : list (list Z)) (pp cc bb : Z) (s : astate) (c n : Z) (ns : bool) (res : option (list Z) * astate) : Prop :=
let (o, s') := res in
match o with
| None => exists r', s' = upd_reg c r' s /\ WfP U (pp - 1) cc bb s' /\ ns = false /\ carve_x s c r'
| Some tops => exists r2 rest,
carve_x s c r2 /\
WfP U (pp - 1) cc bb (upd_reg c r2 s) /\
s' = upd_reg c (mkRegion (rg_mapped_user r2) (rg_alloc_user r2) (rg_mapped_fa r2) rest (rg_holes r2)) s /\
runs_ok rest /\ fa_elems (class_size c) (rg_free r2) = tops ++ fa_elems (class_size c) rest /\
Z.of_nat (length tops) = n /\ fa_len rest = fa_len (rg_free r2) - n
end.
Lemma get_from_allocator_okx : forall U pp cc bb s c n ns,
WfP U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> 1 <= n -> n * class_size c <= kMaxSize -> n <= 8 ->
(fa_len (rg_free (reg s c)) < n -> rg_mapped_user (reg s c) + kUserMapSize <= kUserMapSize * EV_MAX /\
(st_nev s <= EV_MAX \/ rg_alloc_user (reg s c) <= class_size c * (65536 - 10240))) ->
atok ns (get_from_allocator c n s) (gfa_postx U pp cc bb s c n).
Proof.
intros U pp cc bb s c n ns W Hc Hpp Hn Hnsz Hn8 Hroom.
assert (HL : (Z.to_nat c < length (st_regions s))%nat) by (eapply WfP_len_regions; [exact W | lia]).
assert (ES : upd_reg c (reg s c) s = s) by (apply upd_reg_same; [lia | exact HL]).
pose proof (class_ok c Hc) as (Ksz & _).
pose proof (wf_classes _ _ _ _ _ W c Hc) as C0. unfold wf_class in C0.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ C0)) as FL0.
unfold get_from_allocator. apply atok_bind. apply atok_get_region. cbn [fst snd].
apply atok_bind.
apply (atok_mono _ _ (fun ns1 (res : bool * astate) => let (ok, s1) := res in exists r1, s1 = upd_reg c r1 s /\ WfP U (pp - 1) cc bb s1 /\
(ok = true -> n <= fa_len (rg_free r1)) /\ (ok = false -> ns1 = false) /\ carve_x s c r1)).
2:{ destruct (Z.ltb_spec (fa_len (rg_free (reg s c))) n) as [Hlt|Hge].
- eapply atok_mono; [|apply (populate_okx U pp cc bb s c (n - fa_len (rg_free (reg s c))) ns W Hc Hpp); [lia | nia | lia | exact (proj1 (Hroom Hlt)) | exact (proj2 (Hroom Hlt))]].
intros ns1 [ok s1] (r1 & -> & W1 & F1 & OK1 & NS1 & CV1). exists r1. splits; [reflexivity | exact W1 | intros Hok; specialize (OK1 Hok); lia | exact NS1 | exact CV1].
- apply atok_ret. exists (reg s c). rewrite ES. pose proof (wf_slack _ _ _ _ _ W). splits; [reflexivity | eapply WfP_weaken; [exact W|lia|lia|lia] | intros _; lia | intros; discriminate | unfold carve_x; splits; lia]. }
intros ns1 [ok s1] (r1 & -> & W1 & OK1 & NS1 & CV1). cbn [fst snd].
destruct ok; cbn [negb].
2:{ apply atok_ret. exists r1. splits; [reflexivity | exact W1 | exact (NS1 eq_refl) | exact CV1]. }
specialize (OK1 eq_refl).
apply atok_bind. apply atok_get_region. rewrite reg_upd_reg by (lia || exact HL). cbn [fst snd].
destruct (Z.ltb_spec (fa_len (rg_free r1)) n) as [Hlt|_]; [lia|].
pose proof (wf_classes _ _ _ _ _ W1 c Hc) as C1. unfold wf_class in C1. rewrite reg_upd_reg in C1 by (lia || exact HL).
pose proof (wr_runs _ _ _ _ _ _ C1) as R1.
destruct (fa_pop_n_some 10000 (class_size c) n (rg_free r1) [] R1) as (tops & rest & Ep); [lia | change (Z.of_nat 10000) with 10000; lia |].
assert (Hn0 : 0 <= n) by lia.
rewrite Ep. destruct (fa_pop_n_spec _ _ _ _ _ _ _ R1 Hn0 Ep) as (E1 & E2 & E3 & E4). cbn [rev app length] in E1, E4.
apply atok_bind. apply atok_set_region. cbn [fst snd]. apply atok_ret.
exists r1, rest. rewrite upd_reg_upd_reg. splits; auto.
Qed.
Lemma get_from_allocator_ok : forall U pp cc bb s c n ns,
WfP U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> 1 <= n -> n * class_size c <= kMaxSize -> n <= 8 ->
(fa_len (rg_free (reg s c)) < n -> rg_mapped_user (reg s c) + kUserMapSize <= kUserMapSize * EV_MAX /\
(st_nev s <= EV_MAX \/ rg_alloc_user (reg s c) <= class_size c * (65536 - 10240))) ->
atok ns (get_from_allocator c n s) (gfa_post U pp cc bb s c n).
Proof.
intros U pp cc bb s c n ns W Hc Hpp Hn Hnsz Hn8 Hroom.
eapply atok_mono; [|exact (get_from_allocator_okx U pp cc bb s c n ns W Hc Hpp Hn Hnsz Hn8 Hroom)].
intros b [[tops|] s'].
- intros (r2 & rest & _ & H). exists r2, rest. exact H.
- intros (r' & E & W' & NS & _). exists r'. auto.
Qed.
Lemma WfP_set_region_pc : forall U pp cc bb s c r' p' pp',
WfP U pp cc bb s -> 1 <= c <= 31 ->
cls_ok c r' p' (st_cache_inited s) (chunk_offs s c) (batch_offs s c) ->
0 <= pp' ->
prim_user_mapped s - rg_mapped_user (reg s c) + rg_mapped_user r' + kUserMapSize * pp' <= kUserMapSize * st_nev s ->
fa_room (rg_alloc_user r') (length (fa_elems (class_size c) (rg_free r') ++ pc_chunks p' ++ chunk_offs s c ++ batch_offs s c))
(cc + bslack c bb + 2 * (EV_MAX - st_nev s)) (rg_mapped_fa r') ->
(st_nev s <= EV_MAX \/ rg_alloc_user r' = 0 \/ 4 * (rg_alloc_user r' / class_size c) <= rg_mapped_fa r') ->
WfP U pp' cc bb (upd_pc c p' (upd_reg c r' s)).
Proof.
intros U pp cc bb s c r' p' pp' W Hc Hcls Hpp' Hbound Hroom Hcap.
assert (Hlen : (Z.to_nat c < length (st_regions s))%nat) by (rewrite (wf_len_regions _ _ _ _ _ W); lia).
assert (Hlen' : (Z.to_nat c < length (st_cache s))%nat) by (rewrite (wf_len_cache _ _ _ _ _ W); lia).
wf_fields W. unfold upd_pc, upd_reg. constructor; wf_easy.
- cbn [st_regions set_cache set_regions]. rewrite zupd_length. assumption.
- cbn [st_cache st_regions set_cache set_regions]. rewrite zupd_length. assumption.
- unfold reg in *. cbn [st_regions set_cache set_regions]. rewrite znth_zupd_other; [assumption | lia | lia | lia].
- intros c' Hc'. unfold wf_class in *. unfold reg, cache in *. cbn [st_regions st_cache st_cache_inited set_cache set_regions].
change (chunk_offs (set_cache (zupd c p' (st_cache s)) (set_regions (zupd c r' (st_regions s)) s)) c') with (chunk_offs s c').
change (batch_offs (set_cache (zupd c p' (st_cache s)) (set_regions (zupd c r' (st_regions s)) s)) c') with (batch_offs s c').
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite !znth_zupd_same; [exact Hcls | lia | exact Hlen' | lia | exact Hlen].
+ rewrite !znth_zupd_other; [ exact (Xcl c' Hc') | lia | lia | exact Hne | lia | lia | exact Hne].
- change (prim_user_mapped (set_regions (zupd c r' (st_regions s)) s) + kUserMapSize * pp' <= kUserMapSize * st_nev s).
rewrite prim_user_mapped_set_region; [| lia | exact Hlen]. exact Hbound.
- lia.
- intros c' Hc'. unfold class_elems, reg, cache in *. cbn [st_regions st_cache st_nev set_cache set_regions].
change (chunk_offs (set_cache (zupd c p' (st_cache s)) (set_regions (zupd c r' (st_regions s)) s)) c') with (chunk_offs s c').
change (batch_offs (set_cache (zupd c p' (st_cache s)) (set_regions (zupd c r' (st_regions s)) s)) c') with (batch_offs s c').
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite !znth_zupd_same; [exact Hroom | lia | exact Hlen' | lia | exact Hlen].
+ rewrite !znth_zupd_other; [ exact (Xroom c' Hc') | lia | lia | exact Hne | lia | lia | exact Hne].
-
destruct Hcap as [Hs|Hcap]; [left; exact Hs|]. destruct Xreg as [Hs|[HP HC]]; [left; exact Hs|]. right. split; [|exact HC].
intros c' Hc'. unfold reg in *. cbn [st_regions set_cache set_regions]. destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite znth_zupd_same; [exact Hcap | lia | exact Hlen].
+ rewrite znth_zupd_other; [exact (HP c' Hc') | lia | lia | exact Hne].
Qed.
Lemma perm_cache_pop : forall (F B K Bt : list Z) x,
Permutation (F ++ (B ++ [x]) ++ K ++ Bt) ([x] ++ F ++ B ++ K ++ Bt).
Proof.
intros F B K Bt x. cbn [app].
transitivity (F ++ x :: (B ++ K ++ Bt)).
- apply Permutation_app_head. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
- apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma perm_cache_refill : forall (F' B K Bt : list Z) tops,
Permutation ((tops ++ F') ++ [] ++ K ++ Bt) (F' ++ rev tops ++ K ++ Bt).
Proof.
intros. cbn [app]. rewrite <- app_assoc.
transitivity (F' ++ tops ++ K ++ Bt).
- rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_tail. apply Permutation_app_comm.
- apply Permutation_app_head. apply Permutation_app_tail. apply Permutation_rev.
Qed.
Definition regs_only (s s' : astate) : Prop :=
st_chunks s' = st_chunks s /\ st_secs s' = st_secs s /\ st_sec_arr s' = st_sec_arr s /\ st_sec_reserved s' = st_sec_reserved s /\
st_qthread s' = st_qthread s /\ st_qglobal s' = st_qglobal s /\ st_fs s' = st_fs s /\ st_depot s' = st_depot s /\
st_internal_inited s' = st_internal_inited s /\ st_nev s' = st_nev s.
Definition cache_alloc_post (U : list (list Z)) (pp cc bb : Z) (s : astate) (c : Z) (ns : bool) (res : option Z * astate) : Prop :=
let (o, s') := res in
WfP U (pp - 1) cc bb s' /\ regs_only s s' /\ st_cache_inited s' = true /\
match o with
| None => ns = false
| Some off => exists x, off = region_off c + x /\ 0 <= x < 2 ^ 32 /\ x < rg_alloc_user (reg s' c) /\ x mod class_size c = 0 /\
~ In x (class_elems s' c)
end.
Definition cache_alloc_postx (U : list (list Z)) (pp cc bb : Z) (s : astate) (c : Z) (ns : bool) (res : option Z * astate) : Prop :=
cache_alloc_post U pp cc bb s c ns res /\
(forall c', 1 <= c' <= 31 -> cdef (snd res) c' = cdef s c' + (if c' =? c then match fst res with Some _ => class_size c | None => 0 end else 0)) /\
(cdef s c = 0 -> nrecZ s c + 10248 <= 65536 -> BigP s -> BigP (snd res)).
Lemma reg_upd_pc_m : forall c p s c', reg (upd_pc c p s) c' = reg s c'. Proof. reflexivity. Qed.
Lemma chunk_offs_upd_pc_m : forall c p s c', chunk_offs (upd_pc c p s) c' = chunk_offs s c'. Proof. reflexivity. Qed.
Lemma batch_offs_upd_pc_m : forall c p s c', batch_offs (upd_pc c p s) c' = batch_offs s c'. Proof. reflexivity. Qed.
Lemma chunk_offs_upd_reg_m : forall c r s c', chunk_offs (upd_reg c r s) c' = chunk_offs s c'. Proof. reflexivity. Qed.
Lemma batch_offs_upd_reg_m : forall c r s c', batch_offs (upd_reg c r s) c' = batch_offs s c'. Proof. reflexivity. Qed.
Lemma cache_upd_reg_m : forall c r s c', cache (upd_reg c r s) c' = cache s c'. Proof. reflexivity. Qed.
Lemma cdef_ext : forall s s' c, rg_alloc_user (reg s' c) = rg_alloc_user (reg s c) -> length (class_elems s' c) = length (class_elems s c) -> cdef s' c = cdef s c.
Proof. intros s s' c H1 H2. unfold cdef. rewrite H1, H2. reflexivity. Qed.
Lemma chunk_offs_ext : forall s s' c, st_chunks s' = st_chunks s -> chunk_offs s' c = chunk_offs s c.
Proof. intros s s' c H. unfold chunk_offs. rewrite H. reflexivity. Qed.
Lemma batch_offs_ext : forall s s' c, st_qthread s' = st_qthread s -> st_qglobal s' = st_qglobal s -> batch_offs s' c = batch_offs s c.
Proof. intros s s' c H1 H2. unfold batch_offs, all_batches. rewrite H1, H2. reflexivity. Qed.
Lemma nrecZ_regs_only : forall s s' c, regs_only s s' -> nrecZ s' c = nrecZ s c.
Proof.
intros s s' c (H1 & _ & _ & _ & H5 & H6 & _). unfold nrecZ. rewrite (chunk_offs_ext s s' c H1), (batch_offs_ext s s' c H5 H6). reflexivity.
Qed.
Lemma exact_alloc : forall c r p i ko bo,
cls_ok c r p i ko bo -> pc_chunks p = [] ->
rg_alloc_user r - class_size c * Z.of_nat (length (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo)) = 0 ->
rg_alloc_user r = class_size c * (fa_len (rg_free r) + Z.of_nat (length ko + length bo)).
Proof.
intros c r p i ko bo C El D. rewrite El in D. cbn [app] in D. rewrite !length_app, !Nat2Z.inj_add in D.
rewrite (fa_elems_length _ _ (wr_runs _ _ _ _ _ _ C)) in D. rewrite Nat2Z.inj_add. lia.
Qed.
Lemma proom_big : forall c r p i ko bo n,
cls_ok c r p i ko bo -> 0 < class_size c -> pc_chunks p = [] -> fa_len (rg_free r) < n -> n <= 8 ->
rg_alloc_user r - class_size c * Z.of_nat (length (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo)) = 0 ->
class_size c * (Z.of_nat (length ko + length bo) + 8) + 2 ^ 20 <= kUserMapSize * EV_MAX ->
rg_mapped_user r + kUserMapSize <= kUserMapSize * EV_MAX.
Proof.
intros c r p i ko bo n C Hsz El Hfl Hn D HB. pose proof (exact_alloc c r p i ko bo C El D) as EA.
pose proof (wr_carved _ _ _ _ _ _ C) as CV. pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ C)) as F0.
unfold kUserMapSize, kMaxSize, EV_MAX in *. nia.
Qed.
Lemma BigP_carve : forall c r p i ko bo r2,
cls_ok c r p i ko bo -> cls_ok c r2 p i ko bo -> 0 < class_size c -> pc_chunks p = [] ->
rg_alloc_user r2 - rg_alloc_user r = class_size c * (fa_len (rg_free r2) - fa_len (rg_free r)) ->
rg_mapped_fa r <= rg_mapped_fa r2 -> fa_len (rg_free r) <= fa_len (rg_free r2) ->
(fa_len (rg_free r2) = fa_len (rg_free r) \/ fa_len (rg_free r2) <= 8 + 10240) ->
rg_alloc_user r - class_size c * Z.of_nat (length (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo)) = 0 ->
Z.of_nat (length ko + length bo) + 10248 <= 65536 ->
(rg_alloc_user r = 0 \/ 4 * (rg_alloc_user r / class_size c) <= rg_mapped_fa r) ->
rg_alloc_user r2 = 0 \/ 4 * (rg_alloc_user r2 / class_size c) <= rg_mapped_fa r2.
Proof.
intros c r p i ko bo r2 C C2 Hsz El CV MF FL FB D HR HB.
destruct (Z.eq_dec (fa_len (rg_free r2)) (fa_len (rg_free r))) as [Feq|Fne].
- assert (EA : rg_alloc_user r2 = rg_alloc_user r) by (rewrite Feq in CV; lia). rewrite EA. destruct HB as [HB|HB]; [left; exact HB | right; lia].
- right. pose proof (exact_alloc c r p i ko bo C El D) as EA.
assert (E2 : rg_alloc_user r2 = (fa_len (rg_free r2) + Z.of_nat (length ko + length bo)) * class_size c) by nia.
rewrite E2, Z.div_mul by lia.
pose proof (wr_fa_len _ _ _ _ _ _ C2) as L2. pose proof (wr_fa _ _ _ _ _ _ C2) as [F0 Fal]. pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ C)) as N0.
apply Z.mod_divide in Fal as [q Hq]; [|unfold kFreeArrayMapSize; lia]. unfold kFreeArrayMapSize in *.
destruct FB as [FB|FB]; [contradiction|]. nia.
Qed.
Lemma pop_ok : forall U pp cc bb s c l,
WfP U pp cc bb s -> 1 <= c <= 31 -> st_cache_inited s = true -> pc_chunks (cache s c) = l -> l <> [] ->
WfP U pp cc bb (upd_pc c (mkPC (pc_max (cache s c)) (removelast l)) s) /\
0 <= last l 0 < rg_alloc_user (reg s c) /\ last l 0 mod class_size c = 0 /\
~ In (last l 0) (class_elems (upd_pc c (mkPC (pc_max (cache s c)) (removelast l)) s) c).
Proof.
intros U pp cc bb s c l W Hc Hi Hl Hne.
pose proof (wf_classes _ _ _ _ _ W c Hc) as C. unfold wf_class in C. rewrite Hi in C.
pose proof (wr_cache _ _ _ _ _ _ C) as [PM PL].
assert (HP : Permutation (fa_elems (class_size c) (rg_free (reg s c)) ++ pc_chunks (cache s c) ++ chunk_offs s c ++ batch_offs s c)
([last l 0] ++ fa_elems (class_size c) (rg_free (reg s c)) ++ removelast l ++ chunk_offs s c ++ batch_offs s c)).
{ rewrite Hl. rewrite <- (removelast_app_last l 0 Hne) at 1. apply perm_cache_pop. }
assert (C' : cls_ok c (reg s c) (mkPC (pc_max (cache s c)) (removelast l)) true (chunk_offs s c) (batch_offs s c)).
{ eapply (cls_ok_repart c _ _ true _ _ _ _ true _ _ [last l 0]); try exact C; try reflexivity.
- exact (wr_runs _ _ _ _ _ _ C).
- exact (wr_fa_len _ _ _ _ _ _ C).
- cbn [pc_max pc_chunks]. split; [exact PM|]. rewrite removelast_length by exact Hne. rewrite Hl in PL. lia.
- exact HP. }
assert (HLc : (Z.to_nat c < length (st_cache s))%nat) by (eapply WfP_len_cache; [exact W | lia]).
split.
- unfold upd_pc. eapply WfP_set_pc; [exact W | exact Hc | rewrite Hi; exact C' |].
eapply fa_room_xfer; [exact (wf_fa_room _ _ _ _ _ W c Hc) | | apply Z.le_refl].
unfold class_elems. cbn [pc_chunks]. rewrite Hl, !length_app, (removelast_length l Hne) || (rewrite Hl, !length_app, removelast_length by exact Hne). lia.
- destruct (cls_ok_take c _ _ _ _ _ _ _ C HP) as (X1 & X2 & X3 & _).
splits; [lia | lia | exact X2 |].
unfold class_elems. rewrite cache_upd_pc by (lia || exact HLc). cbn [pc_chunks].
change (reg (upd_pc c ?[p] s) c) with (reg s c). change (chunk_offs (upd_pc c ?[p] s) c) with (chunk_offs s c).
change (batch_offs (upd_pc c ?[p] s) c) with (batch_offs s c). exact X3.
Qed.
Lemma regs_only_refl : forall s, regs_only s s.
Proof. intros s. unfold regs_only. repeat split; reflexivity. Qed.
Lemma class_elems_upd_reg : forall s c r, 0 <= c <= 31 -> (Z.to_nat c < length (st_regions s))%nat ->
class_elems (upd_reg c r s) c = fa_elems (class_size c) (rg_free r) ++ pc_chunks (cache s c) ++ chunk_offs s c ++ batch_offs s c.
Proof. intros s c r Hc Hl. unfold class_elems. rewrite reg_upd_reg by (lia || exact Hl). reflexivity. Qed.
Lemma cache_alloc_okx : forall U pp cc bb s c ns,
WfP U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> preg s c ->
atok ns (cache_alloc c s) (cache_alloc_postx U pp cc bb s c).
Proof.
intros U pp cc bb s c ns W Hc Hpp Hreg.
pose proof (class_ok c Hc) as (Ksz & K32 & Kmax & Kmc & Kmc2 & Kmcs).
unfold cache_alloc. apply atok_bind. unfold init_cache_if_needed. apply atok_bind. apply atok_get. cbn [fst snd].
assert (STEP1 : forall s1, WfP U pp cc bb s1 -> st_cache_inited s1 = true -> regs_only s s1 ->
st_regions s1 = st_regions s -> (forall c', 1 <= c' <= 31 -> cdef s1 c' = cdef s c') ->
atok ns ((refill_if_empty c ;; p <- get_pc c ;;
match pc_chunks p with
| [] => ret None
| z :: l0 => set_pc c (mkPC (pc_max p) (removelast (z :: l0))) ;; ret (Some (region_off c + last (z :: l0) 0))
end) s1) (cache_alloc_postx U pp cc bb s c)).
2:{ destruct (st_cache_inited s) eqn:Ei.
- apply atok_ret. apply (STEP1 s W Ei (regs_only_refl s) eq_refl). intros; reflexivity.
- apply atok_put. apply STEP1; [apply WfP_init_caches; [exact W | exact Ei] | reflexivity | unfold regs_only; cbn; repeat split; reflexivity | reflexivity |].
intros c' Hc'. cbn [fst snd]. apply cdef_ext; [reflexivity|]. unfold class_elems. rewrite (cache_after_init s c' ltac:(lia)). reflexivity. }
intros s1 W1 Hi1 RO1 ER1 DEF1.
assert (HL : (Z.to_nat c < length (st_regions s1))%nat) by (eapply WfP_len_regions; [exact W1 | lia]).
assert (HLc : (Z.to_nat c < length (st_cache s1))%nat) by (eapply WfP_len_cache; [exact W1 | lia]).
pose proof (wf_classes _ _ _ _ _ W1 c Hc) as C1. unfold wf_class in C1. rewrite Hi1 in C1.
pose proof (wr_cache _ _ _ _ _ _ C1) as [PM1 PL1].
assert (REG1 : forall c', reg s1 c' = reg s c') by (intros c'; unfold reg; rewrite ER1; reflexivity).
assert (NR1 : nrecZ s1 c = nrecZ s c) by (apply nrecZ_regs_only; exact RO1).
assert (POP : forall ns2 pp' s2, WfP U pp' cc bb s2 -> pp - 1 <= pp' <= pp -> st_cache_inited s2 = true -> regs_only s s2 ->
(pc_chunks (cache s2 c) = [] -> ns2 = false) -> (forall c', 1 <= c' <= 31 -> cdef s2 c' = cdef s c') ->
(cdef s c = 0 -> nrecZ s c + 10248 <= 65536 -> BigP s -> BigP s2) ->
atok ns2 ((p <- get_pc c ;;
match pc_chunks p with
| [] => ret None
| z :: l0 => set_pc c (mkPC (pc_max p) (removelast (z :: l0))) ;; ret (Some (region_off c + last (z :: l0) 0))
end) s2) (cache_alloc_postx U pp cc bb s c)).
{ intros ns2 pp' s2 W2 Hpp' Hi2 RO2 HN2 DEF2 BIG2. apply atok_bind. apply atok_get_pc. cbn [fst snd].
assert (HLc2 : (Z.to_nat c < length (st_cache s2))%nat) by (eapply WfP_len_cache; [exact W2 | lia]).
destruct (pc_chunks (cache s2 c)) as [|o l] eqn:El.
- apply atok_ret. unfold cache_alloc_postx. cbn [fst snd]. split; [|split].
+ cbn. split; [eapply WfP_weaken; [exact W2 | lia | pose proof (wf_slack _ _ _ _ _ W2); lia | pose proof (wf_slack _ _ _ _ _ W2); lia] | split; [exact RO2 | split; [exact Hi2 | exact (HN2 eq_refl)]]].
+ intros c' Hc'. rewrite (DEF2 c' Hc'). destruct (c' =? c); lia.
+ exact BIG2.
- apply atok_bind. apply atok_set_pc. cbn [fst snd]. apply atok_ret.
destruct (pop_ok U pp' cc bb s2 c (o :: l) W2 Hc Hi2 El ltac:(discriminate)) as (W3 & X1 & X2 & X3).
unfold cache_alloc_postx. cbn [fst snd]. split; [|split].
+ cbn -[upd_pc Z.add Z.mul region_off last removelast Z.pow Z.lt Z.le cdef Z.eqb]. split; [|split; [|split]].
* eapply WfP_weaken; [exact W3 | lia | pose proof (wf_slack _ _ _ _ _ W2); lia | pose proof (wf_slack _ _ _ _ _ W2); lia].
* unfold regs_only in *. unfold upd_pc. cbn. exact RO2.
* exact Hi2.
* exists (last (o :: l) 0). split; [reflexivity|].
pose proof (mapped_user_bound U pp' cc bb s2 c W2 Hc). pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ W2 c Hc)).
pose proof (wf_slack _ _ _ _ _ W2).
change (reg (upd_pc c ?[p] s2) c) with (reg s2 c).
splits; [lia | unfold kUserMapSize, EV_MAX in *; nia | lia | exact X2 | exact X3].
+
intros c' Hc'. rewrite <- (DEF2 c' Hc'). unfold cdef. rewrite reg_upd_pc_m.
destruct (Z.eqb_spec c' c) as [->|Hne].
* unfold class_elems. rewrite cache_upd_pc by (lia || exact HLc2). cbn [pc_chunks].
rewrite reg_upd_pc_m, chunk_offs_upd_pc_m, batch_offs_upd_pc_m. rewrite El, !length_app.
rewrite (removelast_length (o :: l)) by discriminate. cbn [length]. lia.
* unfold class_elems. rewrite reg_upd_pc_m, chunk_offs_upd_pc_m, batch_offs_upd_pc_m. unfold upd_pc. rewrite cache_upd_other by lia. lia.
+ intros D0 HR HB c' Hc'. rewrite reg_upd_pc_m. exact (BIG2 D0 HR HB c' Hc'). }
assert (BIGC : forall r2 (s2 : astate), pc_chunks (cache s1 c) = [] ->
cls_ok c r2 (cache s1 c) true (chunk_offs s1 c) (batch_offs s1 c) -> carve_x s1 c r2 ->
(forall c', 1 <= c' <= 31 -> c' <> c -> reg s2 c' = reg s1 c') ->
rg_alloc_user (reg s2 c) = rg_alloc_user r2 -> rg_mapped_fa (reg s2 c) = rg_mapped_fa r2 ->
cdef s c = 0 -> nrecZ s c + 10248 <= 65536 -> BigP s -> BigP s2).
{ intros r2 s2 El C2 (CV & MF & FL & FB) OTH EA EM D0 HR HB c' Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
- rewrite EA, EM. rewrite <- (DEF1 c Hc) in D0. unfold cdef, class_elems in D0. rewrite <- NR1 in HR. unfold nrecZ in HR.
apply (BigP_carve c (reg s1 c) (cache s1 c) true (chunk_offs s1 c) (batch_offs s1 c) r2 C1 C2 Ksz El CV MF FL FB D0 HR).
rewrite REG1. exact (HB c Hc).
- rewrite (OTH c' Hc' Hne), REG1. exact (HB c' Hc'). }
apply atok_bind. unfold refill_if_empty. apply atok_bind. apply atok_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s1 c)) as [|o l] eqn:El.
-
rewrite PM1. apply atok_bind.
assert (N1 : 1 <= max_cached c / 2) by (apply Z.div_le_lower_bound; lia).
assert (N8 : max_cached c / 2 <= 8) by (apply Z.div_le_upper_bound; lia).
assert (N3 : max_cached c / 2 <= max_cached c) by (apply Z.div_le_upper_bound; lia).
assert (ROOM1 : fa_len (rg_free (reg s1 c)) < max_cached c / 2 -> rg_mapped_user (reg s1 c) + kUserMapSize <= kUserMapSize * EV_MAX /\
(st_nev s1 <= EV_MAX \/ rg_alloc_user (reg s1 c) <= class_size c * (65536 - 10240))).
{ intros Hlt. destruct Hreg as [Hsmall | (D0 & HB & HCT)].
- pose proof (mapped_user_bound_small U pp cc bb s1 c W1 Hc) as MB.
destruct RO1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rnev). rewrite Rnev in MB |- *. specialize (MB Hsmall).
split; [unfold kUserMapSize, EV_MAX in *; lia | left; exact Hsmall].
- rewrite <- (DEF1 c Hc) in D0. unfold cdef, class_elems in D0. rewrite <- NR1 in HB, HCT. unfold nrecZ in HB, HCT.
split; [exact (proom_big c (reg s1 c) (cache s1 c) true (chunk_offs s1 c) (batch_offs s1 c) (max_cached c / 2) C1 Ksz El Hlt N8 D0 HB)|].
right. pose proof (exact_alloc c (reg s1 c) (cache s1 c) true (chunk_offs s1 c) (batch_offs s1 c) C1 El D0) as EA.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ C1)) as F0. rewrite EA. nia. }
eapply atok_mono; [|apply (get_from_allocator_okx U pp cc bb s1 c (max_cached c / 2) ns W1 Hc Hpp); [exact N1 | exact Kmcs | exact N8 | exact ROOM1]].
intros ns1 [got s2] Hg. cbn [fst snd]. destruct got as [tops|].
+ destruct Hg as (r2 & rest & CV2 & W2 & -> & Hruns & Hel & Hlen & Hfl).
apply atok_set_pc. cbn [fst snd].
set (r' := mkRegion (rg_mapped_user r2) (rg_alloc_user r2) (rg_mapped_fa r2) rest (rg_holes r2)).
pose proof (wf_classes _ _ _ _ _ W2 c Hc) as C2. unfold wf_class in C2.
rewrite reg_upd_reg in C2 by (lia || exact HL). change (cache (upd_reg c r2 s1) c) with (cache s1 c) in C2.
change (st_cache_inited (upd_reg c r2 s1)) with (st_cache_inited s1) in C2. rewrite Hi1 in C2.
change (chunk_offs (upd_reg c r2 s1) c) with (chunk_offs s1 c) in C2. change (batch_offs (upd_reg c r2 s1) c) with (batch_offs s1 c) in C2.
assert (W3 : WfP U (pp - 1) cc bb (upd_pc c (mkPC (max_cached c) (cache_fill_order tops)) (upd_reg c r' s1))).
{ rewrite <- (upd_reg_upd_reg c r2 r' s1).
eapply (WfP_set_region_pc U (pp - 1) cc bb (upd_reg c r2 s1) c); [exact W2 | exact Hc | | lia | | |].
- change (st_cache_inited (upd_reg c r2 s1)) with (st_cache_inited s1). rewrite Hi1.
change (chunk_offs (upd_reg c r2 s1) c) with (chunk_offs s1 c). change (batch_offs (upd_reg c r2 s1) c) with (batch_offs s1 c).
eapply (cls_ok_repart c r2 (cache s1 c) true _ _ r' _ true _ _ []); try exact C2; try reflexivity.
+ exact Hruns.
+ subst r'. cbnr. pose proof (wr_fa_len _ _ _ _ _ _ C2). lia.
+ cbn [pc_max pc_chunks]. split; [reflexivity|]. unfold cache_fill_order. rewrite length_rev. lia.
+ subst r'. cbnr. rewrite Hel, El. unfold cache_fill_order. cbn [pc_chunks app].
pose proof (perm_cache_refill (fa_elems (class_size c) rest) [] (chunk_offs s1 c) (batch_offs s1 c) tops) as PP. cbn [app] in PP. exact PP.
- rewrite reg_upd_reg by (lia || exact HL). subst r'. cbnr. pose proof (wf_prim_ev _ _ _ _ _ W2) as PE.
unfold kUserMapSize in *. lia.
-
pose proof (wf_fa_room _ _ _ _ _ W2 c Hc) as R. unfold class_elems in R. rewrite !reg_upd_reg in R by (lia || exact HL).
change (cache (upd_reg c r2 s1) c) with (cache s1 c) in R.
change (chunk_offs (upd_reg c r2 s1) c) with (chunk_offs s1 c) in R |- *. change (batch_offs (upd_reg c r2 s1) c) with (batch_offs s1 c) in R |- *.
change (st_nev (upd_reg c r2 s1)) with (st_nev s1) in R |- *.
subst r'. cbnr. eapply fa_room_xfer; [exact R | | apply Z.le_refl].
rewrite Hel, El. unfold cache_fill_order. cbn [pc_chunks]. rewrite !length_app, length_rev. cbn [length]. lia.
-
apply (regime_cap_keep U (pp - 1) cc bb (upd_reg c r2 s1) c _ W2 Hc); rewrite reg_upd_reg by (lia || exact HL); subst r'; cbnr; [reflexivity | lia]. }
eapply (POP ns1 (pp - 1)); [exact W3 | lia | exact Hi1 | unfold regs_only in *; cbn; exact RO1 | | |].
{ unfold upd_pc. rewrite cache_upd_same by (lia || (unfold upd_reg; cbn; exact HLc)). cbn [pc_chunks]. unfold cache_fill_order.
intros E. apply (f_equal (@length Z)) in E. rewrite length_rev in E. cbn in E. lia. }
{
destruct CV2 as (CV2 & _).
intros c' Hc'. rewrite <- (DEF1 c' Hc'). unfold cdef.
destruct (Z.eq_dec c' c) as [->|Hne].
- unfold class_elems. rewrite cache_upd_pc by (lia || exact HLc).
rewrite !reg_upd_pc_m, !reg_upd_reg by (lia || exact HL). rewrite chunk_offs_upd_pc_m, batch_offs_upd_pc_m, chunk_offs_upd_reg_m, batch_offs_upd_reg_m.
subst r'. cbn [rg_alloc_user rg_free pc_chunks]. unfold cache_fill_order. rewrite El, !length_app, length_rev. cbn [length].
pose proof (fa_elems_length (class_size c) _ (wr_runs _ _ _ _ _ _ C2)) as L2. rewrite Hel, length_app, Nat2Z.inj_add in L2.
pose proof (fa_elems_length (class_size c) _ (wr_runs _ _ _ _ _ _ C1)) as L1.
rewrite !Nat2Z.inj_add. nia.
- unfold class_elems. rewrite !reg_upd_pc_m, !reg_upd_reg_other by lia. rewrite chunk_offs_upd_pc_m, batch_offs_upd_pc_m, chunk_offs_upd_reg_m, batch_offs_upd_reg_m.
unfold upd_pc. rewrite cache_upd_other by lia. rewrite cache_upd_reg_m. reflexivity. }
{
apply (BIGC r2); [reflexivity | exact C2 | exact CV2 | | | ].
- intros c' Hc' Hne. rewrite reg_upd_pc_m, reg_upd_reg_other by lia. reflexivity.
- rewrite reg_upd_pc_m, reg_upd_reg by (lia || exact HL). reflexivity.
- rewrite reg_upd_pc_m, reg_upd_reg by (lia || exact HL). reflexivity. }
+ destruct Hg as (r' & -> & W2 & NS & CV2). apply atok_ret.
pose proof (wf_classes _ _ _ _ _ W2 c Hc) as C2. unfold wf_class in C2. rewrite reg_upd_reg in C2 by (lia || exact HL).
change (cache (upd_reg c r' s1) c) with (cache s1 c) in C2. change (st_cache_inited (upd_reg c r' s1)) with (st_cache_inited s1) in C2. rewrite Hi1 in C2.
change (chunk_offs (upd_reg c r' s1) c) with (chunk_offs s1 c) in C2. change (batch_offs (upd_reg c r' s1) c) with (batch_offs s1 c) in C2.
eapply (POP ns1 (pp - 1)); [exact W2 | pose proof (wf_slack _ _ _ _ _ W2); lia | exact Hi1 | unfold regs_only in *; cbn; exact RO1 | intros _; exact NS | |].
*
destruct CV2 as (CV2 & _).
intros c' Hc'. cbn [fst snd]. rewrite <- (DEF1 c' Hc'). unfold cdef. destruct (Z.eq_dec c' c) as [->|Hne].
-- unfold class_elems. rewrite !reg_upd_reg by (lia || exact HL). rewrite cache_upd_reg_m, chunk_offs_upd_reg_m, batch_offs_upd_reg_m.
pose proof (fa_elems_length (class_size c) _ (wr_runs _ _ _ _ _ _ C2)) as L2. pose proof (fa_elems_length (class_size c) _ (wr_runs _ _ _ _ _ _ C1)) as L1.
rewrite !length_app, !Nat2Z.inj_add. nia.
-- unfold class_elems. rewrite !reg_upd_reg_other by lia. reflexivity.
* cbn [fst snd]. apply (BIGC r'); [reflexivity | exact C2 | exact CV2 | | | ].
-- intros c' Hc' Hne. rewrite reg_upd_reg_other by lia. reflexivity.
-- rewrite reg_upd_reg by (lia || exact HL). reflexivity.
-- rewrite reg_upd_reg by (lia || exact HL). reflexivity.
- apply atok_ret. eapply (POP ns pp); [exact W1 | pose proof (wf_slack _ _ _ _ _ W1); lia | exact Hi1 | exact RO1 | cbn [fst snd]; intros E; rewrite E in El; discriminate | exact DEF1 |].
intros _ _ HB c' Hc'. rewrite REG1. exact (HB c' Hc').
Qed.
Lemma cache_alloc_ok : forall U pp cc bb s c ns,
WfP U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> preg s c ->
atok ns (cache_alloc c s) (cache_alloc_post U pp cc bb s c).
Proof.
intros U pp cc bb s c ns W Hc Hpp Hreg.
eapply atok_mono; [|exact (cache_alloc_okx U pp cc bb s c ns W Hc Hpp Hreg)]. intros b a (H & _). exact H.
Qed.
