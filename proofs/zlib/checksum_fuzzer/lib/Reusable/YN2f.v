(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM02 YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0x YO0z
YO14 YO0u YO0q YO0v YO10 YO0y YO0b YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN2b YN2c.
From Stdlib Require Import List.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mreal_by_itok {R} : forall segs (t : itree astate R) c (P : R -> config -> Prop) (Q : R -> Prop),
itok t Q -> mreal segs c t (fun r c' => Q r -> P r c') -> mreal segs c t P.
Proof.
intros segs t c P Q HT HM. eapply mreal_mono; [| exact (mreal_itok segs t c _ Q HM HT)].
intros r c' [H1 H2]. exact (H1 H2).
Qed.
Definition dm_len (n : Z) : Z := page_round (n + IB + UNIT).
Definition dm_am (r : nat) (n : Z) : ameta :=
mkAMeta None None (SP r 0) 0 0 0 63 (page_round (n + IB + UNIT) / 4096) 0 [slot_zero].
Definition dm_rest (n : Z) : M (option sptr) :=
r <- new_region RkMap (page_round (n + IB + UNIT)) ;;
step_seq ;;
og <- alloc_meta ;;
match og with
| None => _ <- ask (KMunmap r (n + IB + UNIT)) ;;
upd_region r (fun rg => mkRegion RkMap (rg_len rg) [] false) ;;
ret None
| Some g =>
setm g (mkAMeta None None (SP r 0) 0 0 0 63 (page_round (n + IB + UNIT) / 4096) 0 [slot_zero]) ;;
s <- get ;;
let ctr := Z.land (st_mmap_counter s + 1) (2^32 - 1) in
put (set_mmap_counter ctr s) ;;
p <- enframe g 0 n ctr FUser ;;
ret (Some p)
end.
Definition dm_k (n : Z) (A : astate) : option sptr * astate -> itree astate (option sptr * astate) :=
fun '(og, s') =>
(match og with
| None => _ <- ask (KMunmap (r0 A) (n + IB + UNIT)) ;;
upd_region (r0 A) (fun rg => mkRegion RkMap (rg_len rg) [] false) ;;
ret None
| Some g =>
setm g (mkAMeta None None (SP (r0 A) 0) 0 0 0 63 (page_round (n + IB + UNIT) / 4096) 0 [slot_zero]) ;;
s <- get ;;
let ctr := Z.land (st_mmap_counter s + 1) (2^32 - 1) in
put (set_mmap_counter ctr s) ;;
p <- enframe g 0 n ctr FUser ;;
ret (Some p)
end : M (option sptr)) s'.
Lemma malloc_direct_tree : forall n A,
size_overflows n = false -> MMAP_THRESHOLD <= n ->
malloc n A = IAsk (KMmapRW (n + IB + UNIT)) A (fun z => (if negb (negb (z =? 0)) then ret None else dm_rest n) A).
Proof.
intros n A Hov Hth. unfold malloc. rewrite Hov. rewrite (proj2 (Z.leb_le _ _) Hth). reflexivity.
Qed.
Lemma dm_rest_eq : forall n A, dm_rest n A = ibind (alloc_meta (A2 A (dm_len n))) (dm_k n A).
Proof. intros n A. reflexivity. Qed.
Definition dm_kill (A : astate) (s : astate) : astate :=
set_regions (lupd (st_regions s) (r0 A)
(mkRegion RkMap (rg_len (nth (r0 A) (st_regions s) (mkRegion RkMap 0 [] false))) [] false)) s.
Lemma dm_k_none : forall n A s,
dm_k n A (None, s) = IAsk (KMunmap (r0 A) (n + IB + UNIT)) s (fun _ => IRet (None, dm_kill A s)).
Proof. intros. reflexivity. Qed.
Definition dm_ctr (s : astate) : Z := Z.land (st_mmap_counter s + 1) (2^32 - 1).
Definition dm_A5 (n : Z) (A : astate) (g : sptr) (s : astate) : astate :=
set_mmap_counter (dm_ctr s) (upd_meta g (MUsed (dm_am (r0 A) n)) s).
Lemma dm_k_some : forall n A g s,
dm_k n A (Some g, s) = ibind (enframe g 0 n (dm_ctr s) FUser (dm_A5 n A g s)) (fun '(p, s6) => IRet (Some p, s6)).
Proof. intros. reflexivity. Qed.
Definition usedf (e : sptr * mslot) : list (sptr * ameta) :=
match e with (p, MUsed am) => [(p, am)] | _ => [] end.
Lemma used_metas_flat : forall s, used_metas s = flat_map usedf (st_metas s).
Proof. reflexivity. Qed.
Lemma NoDup_app_l {X} (l1 l2 : list X) : NoDup (l1 ++ l2) -> NoDup l1.
Proof. intros H. exact (NoDup_app_remove_r _ _ H). Qed.
Lemma flat_usedf_eq : forall (l l1 l2 : list (sptr * mslot)),
map fst l1 = map fst l -> NoDup (map fst (l1 ++ l2)) -> NoDup (map fst l) ->
(forall g am, mlookup (l1 ++ l2) g = Some (MUsed am) <-> mlookup l g = Some (MUsed am)) ->
flat_map usedf (l1 ++ l2) = flat_map usedf l.
Proof.
induction l as [|[k x] l IH]; intros l1 l2 Hk ND ND0 Hiff.
- destruct l1 as [|e l1]; [|discriminate]. cbn in *.
induction l2 as [|[p y] l2 IH2]; [reflexivity|]. cbn.
assert (Hy : forall am, y <> MUsed am).
{ intros am ->. assert (H : mlookup ((p, MUsed am) :: l2) p = Some (MUsed am)) by (cbn; rewrite sptr_eqb_refl; reflexivity).
apply Hiff in H. discriminate. }
rewrite IH2.
+ destruct y; try reflexivity. exfalso. eapply Hy. reflexivity.
+ cbn in ND. inversion ND; assumption.
+ intros g am. split; [|intros H; discriminate]. intros H.
apply (Hiff g am). cbn. destruct (sptr_eqb g p) eqn:E; [|exact H].
apply sptr_eqb_eq in E. subst g. exfalso. apply mlookup_In_keys in H. cbn in ND. inversion ND; subst. auto.
- destruct l1 as [|[k' y] l1]; [discriminate|]. cbn in Hk. injection Hk as -> Hk.
cbn [app flat_map].
assert (NDt : NoDup (map fst (l1 ++ l2))) by (cbn in ND; inversion ND; assumption).
assert (Hnk : ~ In k (map fst (l1 ++ l2))) by (cbn in ND; inversion ND; assumption).
assert (Hnk0 : ~ In k (map fst l)) by (cbn in ND0; inversion ND0; assumption).
rewrite (IH l1 l2 Hk NDt).
+ f_equal. specialize (Hiff k). cbn in Hiff. rewrite sptr_eqb_refl in Hiff.
destruct x as [xp xn| |amx]; destruct y as [yp yn| |amy]; try reflexivity;
try (pose proof (proj1 (Hiff amy) eq_refl) as E; discriminate E);
try (pose proof (proj2 (Hiff amx) eq_refl) as E; discriminate E).
pose proof (proj1 (Hiff amy) eq_refl) as E. injection E as ->. reflexivity.
+ cbn in ND0. inversion ND0; assumption.
+ intros g am. specialize (Hiff g am). cbn in Hiff. destruct (sptr_eqb g k) eqn:E; [|exact Hiff].
apply sptr_eqb_eq in E. subst g. split; intros H; exfalso; apply mlookup_In_keys in H; auto.
Qed.
Lemma used_metas_same : forall s s' ext,
NoDup (keys s') -> keys s' = keys s ++ ext ->
(forall g am, MT s' g = Some (MUsed am) <-> MT s g = Some (MUsed am)) ->
used_metas s' = used_metas s.
Proof.
intros s s' ext ND Hk Hiff. rewrite !used_metas_flat. unfold keys, MT in *.
assert (Hk1 : map fst (firstn (length (st_metas s)) (st_metas s')) = map fst (st_metas s)).
{ rewrite <- firstn_map, Hk, firstn_app, length_map, Nat.sub_diag, firstn_O, app_nil_r.
rewrite <- (length_map fst (st_metas s)). apply firstn_all. }
rewrite <- (firstn_skipn (length (st_metas s)) (st_metas s')) in ND, Hiff |- *.
apply flat_usedf_eq; [exact Hk1 | exact ND | | exact Hiff].
rewrite map_app in ND. apply NoDup_app_l in ND. rewrite Hk1 in ND. exact ND.
Qed.
Section h.
Variables (A : astate) (n : Z).
Hypothesis HW : WF A.
Hypothesis Hn : MMAP_THRESHOLD <= n.
Definition dlen : Z := dm_len n.
Definition dA2 : astate := A2 A dlen.
Lemma dlen_facts : 0 < dlen /\ dlen mod PGSZ = 0 /\ n + IB + UNIT <= dlen /\ dlen < n + IB + UNIT + PGSZ /\ 131072 <= dlen.
Proof.
unfold dlen, dm_len. pose proof (page_round_ge (n + IB + UNIT)). pose proof (page_round_mod (n + IB + UNIT)).
pose proof (page_round_lt (n + IB + UNIT)).
unfold MMAP_THRESHOLD, IB, UNIT, PGSZ in *. repeat split; try lia.
Qed.
Lemma dlen_pos : 0 < dlen /\ dlen mod PGSZ = 0.
Proof. pose proof dlen_facts. tauto. Qed.
Lemma dA2_inv : Inv [] None U0 dA2.
Proof. apply Inv_A2; [apply dlen_pos | exact HW]. Qed.
Lemma dA2_region : region_of dA2 (r0 A) = Some (rgn dlen).
Proof. unfold dA2. rewrite (region_of_A2 A dlen dlen_pos). rewrite Nat.ltb_irrefl, Nat.eqb_refl. reflexivity. Qed.
Lemma dA2_usedX : forall q a, usedX [] dA2 q a <-> usedX [] A q a.
Proof. intros q a. unfold usedX, MTX, MT, dA2. rewrite A2_metas. tauto. Qed.
Lemma fresh : forall q a, usedX [] A q a -> (prid (am_mem a) < r0 A)%nat.
Proof. intros q a Hu. exact (used_group_prid_lt _ _ _ _ q a HW Hu). Qed.
Lemma dA2_fields :
st_metas dA2 = st_metas A /\ st_areas dA2 = st_areas A /\ st_usage dA2 = st_usage A /\
st_meta_alloc_shift dA2 = st_meta_alloc_shift A /\ st_avail_meta_areas dA2 = st_avail_meta_areas A /\
st_mmap_counter dA2 = st_mmap_counter A /\ st_init_done dA2 = st_init_done A /\
st_regions dA2 = st_regions A ++ [rgn dlen] /\ st_brk dA2 = st_brk A /\ st_active dA2 = st_active A.
Proof. unfold dA2, A2, seqf, A1. destruct (st_seq _ =? 255); repeat split; reflexivity. Qed.
Lemma dA2_bounded : bounded A -> bounded dA2.
Proof.
pose proof dA2_fields as (E1 & E2 & E3 & E4 & _). unfold bounded, usage_of. rewrite E2, E3, E4. tauto.
Qed.
Lemma dA2_ama : ama_ok A -> ama_ok dA2.
Proof.
pose proof dA2_fields as (_ & E2 & _ & _ & E5 & _ & _ & E8 & _). unfold ama_ok. rewrite E2, E5, E8, length_app. cbn. intros H H'. specialize (H H'). lia.
Qed.
Definition am_post (r : option sptr * astate) : Prop :=
am_frame dA2 (snd r) /\ ub_same dA2 (snd r) /\
match fst r with
| None => Inv [] None U0 (snd r) /\ (forall g am, usedX [] (snd r) g am <-> usedX [] A g am)
| Some m => Inv [m] None U0 (snd r) /\ In m (keys (snd r)) /\
(MT (snd r) m = Some MRaw \/ MT (snd r) m = Some (MFree None None)) /\
(forall g am, usedX [m] (snd r) g am <-> usedX [] A g am)
end.
Lemma alloc_meta_facts : itok (alloc_meta dA2) am_post.
Proof.
eapply alloc_meta_spec; [exact dA2_inv | |].
- intros s' HI Fr EU UB. split; [exact Fr|]. split; [exact UB|]. cbn [fst snd]. split; [exact HI|].
intros g am. rewrite EU. apply dA2_usedX.
- intros m s' HI _ Kg Mg Fr EU UB. split; [exact Fr|]. split; [exact UB|]. cbn [fst snd].
split; [exact HI|]. split; [exact Kg|]. split; [exact Mg|]. intros g am. rewrite EU. apply dA2_usedX.
Qed.
End h.
Definition enframe_pure (am : ameta) (g : sptr) (idx n : Z) (k : fkind) (off0 : Z) (s : astate) : sptr * astate :=
let stride := stride_of am in
let slack := (stride - IB - n) / UNIT in
let off := fold_off slack off0 in
let reserved := stride - IB - UNIT * off - n in
let rsv := if 5 <=? reserved then 5 else reserved in
let hdr := if off =? 0
then (match k with FUser => idx + rsv * 32 | FGroup => idx + 192 end, (stride * idx) / UNIT)
else (224, off) in
(padd (slot_start am idx) (UNIT * off),
upd_meta g (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n k))))) s).
Lemma getm_eval s g am : MT s g = Some (MUsed am) -> getm g s = IRet (am, s).
Proof. intros H. unfold getm, bind, get. cbn [ibind]. unfold MT in H. rewrite H. reflexivity. Qed.
Lemma bind_IRet {X Y} (mm : M X) (kk : X -> M Y) s a s' : mm s = IRet (a, s') -> bind mm kk s = kk a s'.
Proof. intros H. unfold bind. rewrite H. reflexivity. Qed.
Lemma enframe_eval s g am idx n ctr k h3 h16 :
MT s g = Some (MUsed am) -> 0 <= idx <= am_last am -> ss_hdr (nth_slot am idx) = Some (h3, h16) ->
let slack := (stride_of am - IB - n) / UNIT in
let off0 := if slack =? 0 then 0 else Z.land (if h3 =? 0 then ctr else h16 + 1) 255 in
0 <= fold_off slack off0 <= slack ->
enframe g idx n ctr k s = IRet (enframe_pure am g idx n k off0 s).
Proof.
intros Hm Hidx Hh slack off0 Hoff. unfold enframe.
rewrite (bind_IRet (getm g) _ s am s (getm_eval s g am Hm)).
rewrite (bind_IRet (mcheck _ 12) _ s tt s) by (unfold mcheck; rewrite (proj2 (Z.leb_le 0 idx)), (proj2 (Z.leb_le idx _)) by lia; reflexivity).
cbv zeta. fold slack.
match goal with |- bind ?m0 _ s = _ => rewrite (bind_IRet m0 _ s off0 s) end.
2:{ subst off0. destruct (slack =? 0); [reflexivity|]. rewrite Hh. reflexivity. }
match goal with |- bind (massert (?o <=? _) _) _ s = _ => change o with (fold_off slack off0) end.
rewrite (bind_IRet (massert _ 4) _ s tt s) by (unfold massert; rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity).
unfold enframe_pure. cbv zeta. fold slack. reflexivity.
Qed.
Lemma nslots_kill_list : forall l r rg,
nth_error l r = Some rg -> rg_live rg = true -> rg_kind rg = RkMap ->
fold_right (fun rg acc => region_slots rg + acc) 0 (lupd l r (YO0i.mkRegion RkMap (rg_len rg) [] false)) =
fold_right (fun rg acc => region_slots rg + acc) 0 l - 1.
Proof.
induction l as [|x l IH]; intros r rg Hr Hl Hk; [destruct r; discriminate|].
destruct r as [|r]; cbn [nth_error] in Hr; cbn [lupd fold_right].
- injection Hr as ->. unfold region_slots at 1 3. rewrite Hl, Hk. cbn. lia.
- rewrite (IH r rg Hr Hl Hk). lia.
Qed.
Section i.
Variables (A : astate) (n : Z) (A3 : astate).
Hypothesis HW : WF A.
Hypothesis Hn : MMAP_THRESHOLD <= n.
Hypothesis FR : am_frame (dA2 A n) A3.
Hypothesis UB : ub_same (dA2 A n) A3.
Let len := dlen n.
Lemma A3_region : region_of A3 (r0 A) = Some (rgn len).
Proof. destruct FR as (_ & _ & Hr & _). apply Hr; [apply dA2_region; assumption | reflexivity]. Qed.
Lemma A3_regions_len : (r0 A < length (st_regions A3))%nat.
Proof. exact (region_of_lt _ _ _ A3_region). Qed.
Lemma A3_used_metas : forall X, Inv X None U0 A3 ->
(forall g am, memb g X = true -> MT A3 g <> Some (MUsed am)) ->
(forall g am, usedX X A3 g am <-> usedX [] A g am) ->
used_metas A3 = used_metas A.
Proof.
intros X HI HX EU. destruct UB as (ext & Hk & _ & _).
rewrite <- (used_metas_A2 A len). apply (used_metas_same _ _ ext (proj1 (inv_keys HI))).
- exact Hk.
- intros g am. unfold dA2 in EU. fold len in EU. split; intros H.
+ assert (Hu : usedX X A3 g am).
{ apply usedX_intro; [|exact H]. destruct (memb g X) eqn:E; [|reflexivity]. exfalso. exact (HX g am E H). }
apply EU in Hu. apply usedX_MT in Hu. destruct Hu as [Hu _]. unfold MT in *. rewrite A2_metas. exact Hu.
+ assert (Hu : usedX [] A g am) by (apply usedX_intro; [reflexivity | unfold MT in *; rewrite A2_metas in H; exact H]).
apply EU in Hu. exact (proj1 (usedX_MT _ _ _ _ Hu)).
Qed.
Section j.
Hypothesis HI3 : Inv [] None U0 A3.
Hypothesis EU3 : forall g am, usedX [] A3 g am <-> usedX [] A g am.
Let A4 := dm_kill A A3.
Lemma kill_region_of : forall k,
region_of A4 k = if Nat.eqb k (r0 A) then Some (mkRegion RkMap len [] false) else region_of A3 k.
Proof.
intros k. unfold A4, dm_kill. rewrite region_of_upd.
pose proof A3_region as Hr. unfold region_of in Hr. rewrite (nth_error_nth _ _ (mkRegion RkMap 0 [] false) Hr). cbn [rg_len rgn].
rewrite (proj2 (Nat.ltb_lt _ _) A3_regions_len), andb_true_r. reflexivity.
Qed.
Lemma kill_inv : Inv [] None U0 A4.
Proof.
unfold A4, dm_kill. pose proof A3_region as Hr.
unfold region_of in Hr. rewrite (nth_error_nth _ _ (mkRegion RkMap 0 [] false) Hr). cbn [rg_len rgn].
change len with (rg_len (rgn len)). apply (Inv_kill_map [] None U0 A3 (r0 A) (rgn len) HI3 A3_region eq_refl).
intros q a Hu _ E. apply EU3 in Hu. pose proof (fresh A HW q a Hu). lia.
Qed.
Lemma kill_fields : st_metas A4 = st_metas A3 /\ st_areas A4 = st_areas A3 /\ st_usage A4 = st_usage A3 /\
st_meta_alloc_shift A4 = st_meta_alloc_shift A3 /\ st_avail_meta_areas A4 = st_avail_meta_areas A3 /\
length (st_regions A4) = length (st_regions A3) /\ st_brk A4 = st_brk A3 /\ st_init_done A4 = st_init_done A3 /\
st_mmap_counter A4 = st_mmap_counter A3 /\ st_seq A4 = st_seq A3 /\ st_unmap_seq A4 = st_unmap_seq A3.
Proof. unfold A4, dm_kill. cbn. rewrite length_lupd. repeat split; reflexivity. Qed.
Lemma kill_used_metas : used_metas A4 = used_metas A.
Proof.
transitivity (used_metas A3); [unfold used_metas; rewrite (proj1 kill_fields); reflexivity|].
apply (A3_used_metas [] HI3); [intros g am H; discriminate | exact EU3].
Qed.
Lemma kill_image : image A4 = image A3.
Proof.
unfold image. rewrite (areas_cells_metas A3 A4 _ (proj1 kill_fields)).
replace (ctx_cells A4) with (ctx_cells A3) by (unfold A4, dm_kill; destruct A3; reflexivity).
replace (used_metas A4) with (used_metas A3) by (unfold used_metas; rewrite (proj1 kill_fields); reflexivity).
rewrite (proj1 (proj2 kill_fields)). reflexivity.
Qed.
Lemma kill_bounded : bounded A3 -> bounded A4.
Proof. pose proof kill_fields as (E1 & E2 & E3 & E4 & _). unfold bounded, usage_of. rewrite E2, E3, E4. tauto. Qed.
Lemma kill_ama : ama_ok A3 -> ama_ok A4.
Proof. pose proof kill_fields as (_ & E2 & _ & _ & E5 & E6 & _). unfold ama_ok. rewrite E2, E5, E6. tauto. Qed.
Lemma kill_nslots : nslots A4 = nslots A3 - 1.
Proof.
unfold nslots, A4, dm_kill. cbn [st_regions set_regions].
pose proof A3_region as Hr. unfold region_of in Hr. rewrite (nth_error_nth _ _ (mkRegion RkMap 0 [] false) Hr). cbn [rg_len rgn].
change len with (rg_len (rgn len)). apply (nslots_kill_list _ _ _ Hr eq_refl eq_refl).
Qed.
Lemma kill_live_bytes : live_bytes A4 = live_bytes A3 - len.
Proof.
apply (live_bytes_kill A3 A4 (r0 A) (rgn len) A3_region eq_refl). intros k. rewrite kill_region_of. reflexivity.
Qed.
End j.
Section u.
Variable m : sptr.
Hypothesis HI3 : Inv [m] None U0 A3.
Hypothesis Km : In m (keys A3).
Hypothesis Mm : MT A3 m = Some MRaw \/ MT A3 m = Some (MFree None None).
Hypothesis EU3 : forall g am, usedX [m] A3 g am <-> usedX [] A g am.
Hypothesis Hn62 : n < 2 ^ 62.
Definition maplen : Z := len / 4096.
Definition am4 : ameta := direct_am (r0 A) maplen.
Definition A4s : astate := upd_meta m (MUsed am4) A3.
Definition ctr5 : Z := dm_ctr A3.
Definition A5 : astate := set_mmap_counter ctr5 A4s.
Lemma maplen_facts : len = maplen * PGSZ /\ 32 <= maplen < 2 ^ 51.
Proof.
pose proof (dlen_facts n Hn) as (H1 & H2 & H3 & H4 & H5). fold len in H1, H2, H3, H4, H5.
unfold maplen, PGSZ, MMAP_THRESHOLD, IB, UNIT in *. pose proof (Z_div_mod_eq_full len 4096).
split; [lia|]. split.
- apply Z.div_le_lower_bound; lia.
- apply Z.div_lt_upper_bound; lia.
Qed.
Lemma am4_eq : dm_am (r0 A) n = am4.
Proof. reflexivity. Qed.
Lemma A5_eq : dm_A5 n A m A3 = A5.
Proof. reflexivity. Qed.
Lemma m_not_used : forall am, MT A3 m <> Some (MUsed am).
Proof. intros am H. destruct Mm as [E|E]; rewrite E in H; discriminate. Qed.
Lemma A3_used_metas_some : used_metas A3 = used_metas A.
Proof.
apply (A3_used_metas [m] HI3); [| exact EU3].
intros g am Hg. cbn in Hg. destruct (sptr_eqb g m) eqn:E; [|discriminate]. apply sptr_eqb_eq in E. subst g. apply m_not_used.
Qed.
Lemma fresh3 : forall q a, usedX [m] A3 q a -> prid (am_mem a) <> r0 A.
Proof. intros q a Hu E. apply EU3 in Hu. pose proof (fresh A HW q a Hu). lia. Qed.
Lemma install_facts : Inv [] (Some (m, 0)) U0 A4s /\ usedX [] A4s m am4 /\ ub_same A3 A4s.
Proof.
pose proof maplen_facts as (Hml & Hml2).
pose proof (install_direct_spec [] U0 A3 m (r0 A) (rgn len) maplen
(fun r => Inv [] (Some (m, 0)) U0 (snd r) /\ usedX [] (snd r) m am4 /\ ub_same A3 (snd r))
HI3 eq_refl A3_region eq_refl eq_refl Hml ltac:(lia) fresh3) as H.
cbn [itok setm modify snd] in H. apply H. intros s' -> HI U UB'. auto.
Qed.
Lemma ctr5_range : 0 <= ctr5 < 2 ^ 32.
Proof.
unfold ctr5, dm_ctr. apply land32_range.
pose proof (inv_ctx HI3) as (_&_&_&_&_&_&_&_&C9&_). lia.
Qed.
Lemma A5_inv : Inv [] (Some (m, 0)) U0 A5 /\ usedX [] A5 m am4.
Proof.
destruct install_facts as (HI4 & U4 & _). split.
- unfold A5. apply Inv_set_mmap_counter; [exact HI4 | apply ctr5_range].
- unfold usedX, MTX, MT, A5 in *. cbn. exact U4.
Qed.
Lemma A5_fields :
st_metas A5 = mupdate (st_metas A3) m (MUsed am4) /\ st_areas A5 = st_areas A3 /\ st_regions A5 = st_regions A3 /\
st_usage A5 = st_usage A3 /\ st_meta_alloc_shift A5 = st_meta_alloc_shift A3 /\ st_avail_meta_areas A5 = st_avail_meta_areas A3 /\
st_mmap_counter A5 = ctr5 /\ st_init_done A5 = st_init_done A3 /\ st_brk A5 = st_brk A3 /\
st_seq A5 = st_seq A3 /\ st_unmap_seq A5 = st_unmap_seq A3 /\ keys A5 = keys A3.
Proof.
unfold A5, A4s, upd_meta. cbn. repeat split; try reflexivity.
unfold keys. cbn. apply map_fst_mupdate_In. exact Km.
Qed.
Definition e_stride : Z := maplen * 4096 - UNIT.
Definition e_slack : Z := (e_stride - IB - n) / UNIT.
Definition e_off0 : Z := if e_slack =? 0 then 0 else Z.land ctr5 255.
Definition e_off : Z := fold_off e_slack e_off0.
Definition e_reserved : Z := e_stride - IB - UNIT * e_off - n.
Definition e_rsv : Z := if 5 <=? e_reserved then 5 else e_reserved.
Definition e_hdr : Z * Z := if e_off =? 0 then (e_rsv * 32, 0) else (224, e_off).
Definition e_fr : frame := mkFrame e_off n FUser.
Definition am6 : ameta := upd_slot am4 0 (mkSlot (Some e_hdr) (Some e_fr)).
Definition A6 : astate := upd_meta m (MUsed am6) A5.
Definition p6 : sptr := SP (r0 A) (UNIT + UNIT * e_off).
Lemma stride_am4 : stride_of am4 = e_stride.
Proof.
pose proof maplen_facts as (_ & Hml). unfold stride_of, am4, direct_am, e_stride. cbn [am_last am_maplen].
destruct (maplen =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.
Lemma e_facts : 0 <= e_slack /\ UNIT * e_slack <= e_stride - IB - n /\ 0 <= e_off0 < 256 /\
0 <= e_off <= e_slack /\ e_off <= 255 /\ 0 <= e_reserved < PGSZ /\ 0 <= e_rsv <= 5 /\
e_stride = len - UNIT /\ n + IB + UNIT <= len.
Proof.
pose proof maplen_facts as (Hml & Hml2). pose proof (dlen_facts n Hn) as (D1 & D2 & D3 & D4 & D5). fold len in D1, D2, D3, D4, D5.
assert (Es : e_stride = len - UNIT) by (unfold e_stride, UNIT, PGSZ in *; lia).
assert (Hsl : 0 <= e_slack) by (unfold e_slack; apply Z.div_pos; unfold IB, UNIT in *; lia).
assert (Hsl2 : UNIT * e_slack <= e_stride - IB - n).
{ unfold e_slack, UNIT. pose proof (Z.mul_div_le (e_stride - IB - n) 16 ltac:(lia)). unfold IB, UNIT in *. lia. }
assert (Ho0 : 0 <= e_off0 < 256).
{ unfold e_off0. destruct (e_slack =? 0); [lia|]. pose proof (Z.land_nonneg ctr5 255).
pose proof (land255_range ctr5). pose proof ctr5_range. lia. }
pose proof (fold_off_ok e_slack e_off0 Hsl Ho0) as Ho. fold e_off in Ho.
pose proof (fold_off_le e_slack e_off0 ltac:(lia) Hsl) as Hole. fold e_off in Hole.
assert (Hr : 0 <= e_reserved < PGSZ).
{ unfold e_reserved. pose proof (Z_div_mod_eq_full (e_stride - IB - n) 16). pose proof (Z.mod_pos_bound (e_stride - IB - n) 16 ltac:(lia)).
unfold e_slack, IB, UNIT, PGSZ in *. nia. }
unfold e_rsv. destruct (Z.leb_spec 5 e_reserved); repeat split; unfold PGSZ, IB, UNIT in *; lia.
Qed.
Lemma enframe_direct_eval : enframe m 0 n ctr5 FUser A5 = IRet (p6, A6).
Proof.
pose proof e_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
destruct A5_inv as [HI5 U5].
rewrite (enframe_eval A5 m am4 0 n ctr5 FUser 0 0 (proj1 (usedX_MT _ _ _ _ U5)) ltac:(cbn; lia) eq_refl).
2:{ rewrite stride_am4. fold e_slack. change (Z.land (if 0 =? 0 then ctr5 else 0 + 1) 255) with (Z.land ctr5 255). fold e_off0. fold e_off. lia. }
unfold enframe_pure. rewrite stride_am4. cbv zeta. fold e_slack.
change (Z.land (if 0 =? 0 then ctr5 else 0 + 1) 255) with (Z.land ctr5 255). fold e_off0. fold e_off. fold e_reserved. fold e_rsv.
unfold p6, A6, am6, e_hdr, e_fr. rewrite Z.add_0_l, Z.mul_0_r. change (0 / UNIT) with 0.
f_equal. f_equal. unfold slot_start, am4, direct_am. cbn [am_mem padd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
Lemma A6_fields :
st_metas A6 = mupdate (st_metas A5) m (MUsed am6) /\ st_areas A6 = st_areas A3 /\ st_regions A6 = st_regions A3 /\
st_usage A6 = st_usage A3 /\ st_meta_alloc_shift A6 = st_meta_alloc_shift A3 /\ st_avail_meta_areas A6 = st_avail_meta_areas A3 /\
st_mmap_counter A6 = ctr5 /\ st_init_done A6 = st_init_done A3 /\ st_brk A6 = st_brk A3 /\
st_seq A6 = st_seq A3 /\ st_unmap_seq A6 = st_unmap_seq A3 /\ keys A6 = keys A3.
Proof.
unfold A6, A5, A4s, upd_meta. cbn. repeat split; try reflexivity.
unfold keys. cbn. rewrite !map_fst_mupdate_In; [reflexivity | exact Km |]. rewrite map_fst_mupdate_In by exact Km. exact Km.
Qed.
Lemma MT_A6 : forall g, MT A6 g = if sptr_eqb g m then Some (MUsed am6) else MT A3 g.
Proof.
intros g. unfold A6. rewrite MT_upd. destruct (sptr_eqb g m) eqn:E; [reflexivity|].
unfold MT, A5, A4s, upd_meta. cbn. rewrite mlookup_mupdate. rewrite E. reflexivity.
Qed.
Lemma footprint_A6 : footprint A6 = footprint A3.
Proof. unfold footprint, region_of. rewrite (proj1 (proj2 A6_fields)), (proj1 (proj2 (proj2 A6_fields))). reflexivity. Qed.
Lemma live_bytes_A6 : live_bytes A6 = live_bytes A3.
Proof. unfold live_bytes. rewrite (proj1 (proj2 (proj2 A6_fields))). reflexivity. Qed.
Lemma nslots_A6 : nslots A6 = nslots A3.
Proof. unfold nslots. rewrite (proj1 (proj2 (proj2 A6_fields))). reflexivity. Qed.
Lemma region_of_A6 : forall k, region_of A6 k = region_of A3 k.
Proof. intros k. unfold region_of. rewrite (proj1 (proj2 (proj2 A6_fields))). reflexivity. Qed.
Definition new_cells : list mcell :=
MCell (LCtx CTX_mmap_counter) 4 (VZ ctr5)
:: meta_slot_cells m (Some (MUsed am6)) ++ group_cells m am6.
Lemma used_metas_A6 : forall g am, In (g, am) (used_metas A6) -> (g = m /\ am = am6) \/ In (g, am) (used_metas A3).
Proof.
intros g am Hin. pose proof (proj1 (inv_keys HI3)) as ND.
assert (ND6 : NoDup (keys A6)) by (rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 A6_fields))))))))))); exact ND).
apply (used_metas_iff A6 g am ND6) in Hin. rewrite MT_A6 in Hin.
destruct (sptr_eqb g m) eqn:E.
- apply sptr_eqb_eq in E. left. split; [exact E | congruence].
- right. apply (used_metas_iff A3 g am ND). exact Hin.
Qed.
Lemma ctx_cells_A6 : forall c, In c (ctx_cells A6) -> c = MCell (LCtx CTX_mmap_counter) 4 (VZ ctr5) \/ In c (ctx_cells A3).
Proof.
intros c Hc. unfold ctx_cells in *. unfold A6, A5, A4s, upd_meta in Hc. cbn -[In app Z.add Z.mul Z.of_nat seq map] in Hc.
rewrite !in_app_iff in Hc |- *. cbn [In] in Hc |- *.
destruct Hc as [[H|[H|[H|H]]]|H]; [right; left; auto | right; left; auto | left; symmetry; exact H | right; left; right; right; right; exact H | right; right; exact H].
Qed.
Lemma areas_cells_A6 : forall l c, In c (areas_cells A6 l) -> In c (meta_slot_cells m (Some (MUsed am6))) \/ In c (areas_cells A3 l).
Proof.
induction l as [|a l IH]; intros c Hc; [destruct Hc|].
cbn [areas_cells] in Hc |- *. rewrite in_app_iff in Hc. rewrite in_app_iff.
destruct Hc as [Hc|Hc]; [| destruct (IH c Hc); tauto].
unfold area_cells in Hc |- *. rewrite in_app_iff in Hc. rewrite in_app_iff.
destruct Hc as [Hc|Hc]; [right; left; left; exact Hc|].
apply in_flat_map in Hc as (k & Hk & Hc).
change (mlookup (st_metas A6)) with (MT A6) in Hc. rewrite MT_A6 in Hc.
destruct (sptr_eqb _ m) eqn:E.
- apply sptr_eqb_eq in E. rewrite E in Hc. left. exact Hc.
- right. left. right. apply in_flat_map. exists k. split; [exact Hk|]. exact Hc.
Qed.
Lemma image_A6 : forall c, In c (image A6) -> In c new_cells \/ In c (image A3).
Proof.
intros c Hc. unfold image in Hc |- *. unfold new_cells. rewrite !in_app_iff in Hc. cbn [In]. rewrite !in_app_iff.
destruct Hc as [Hc|[Hc|Hc]].
- destruct (ctx_cells_A6 c Hc); [left; left; symmetry; assumption | tauto].
- rewrite (proj1 (proj2 A6_fields)) in Hc. destruct (areas_cells_A6 _ c Hc); tauto.
- apply in_flat_map in Hc as ([g am] & Hg & Hc). cbn [fst snd] in Hc.
destruct (used_metas_A6 g am Hg) as [[-> ->] | Hg3]; [tauto|].
right. right. right. apply in_flat_map. exists (g, am). auto.
Qed.
Lemma tail_cells_A6 : forall c, In c (tail_cells A6) -> In c (group_tail_cells am6) \/ In c (tail_cells A3).
Proof.
intros c Hc. unfold tail_cells in *. apply in_flat_map in Hc as ([g am] & Hg & Hc). cbn [snd] in Hc.
destruct (used_metas_A6 g am Hg) as [[-> ->] | Hg3]; [left; exact Hc|].
right. apply in_flat_map. exists (g, am). auto.
Qed.
Lemma frames_A6 : forall f, In f (frames A6) -> f = (m, am6, 0, e_fr) \/ In f (frames A3).
Proof.
intros f Hf. unfold frames in *. apply in_flat_map in Hf as ([g am] & Hg & Hf).
destruct (used_metas_A6 g am Hg) as [[-> ->] | Hg3].
- left. cbn in Hf. destruct Hf as [<-|[]]. reflexivity.
- right. apply in_flat_map. exists (g, am). auto.
Qed.
Lemma stride_am6 : stride_of am6 = e_stride.
Proof. unfold am6. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (upd_slot_fields _ _ _)))))). apply stride_am4. Qed.
Definition newc_spec (c : mcell) : Prop :=
(c = MCell (LCtx CTX_mmap_counter) 4 (VZ ctr5)) \/
(exists d (w : nat) v, c = MCell (LMem (padd m d)) w v /\
((d = 0 /\ w = 8%nat /\ v = VZ 0) \/ (d = 8 /\ w = 8%nat /\ v = VZ 0) \/ (d = 16 /\ w = 8%nat /\ v = VP (SP (r0 A) 0)) \/
(d = 24 /\ w = 4%nat /\ v = VZ 0) \/ (d = 28 /\ w = 4%nat /\ v = VZ 0) \/ (d = 32 /\ w = 8%nat /\ v = VZ (bits_enc 0 63 maplen)))) \/
(exists p (w : nat) v, c = MCell (LMem p) w v /\ prid p = r0 A /\
let off := poff p in
((off = 0 /\ w = 8%nat /\ v = VP m) \/ (off = 8 /\ w = 4%nat /\ v = VZ 0) \/ (off = 12 /\ w = 1%nat /\ v = VZ 0) \/
(off = 13 /\ w = 1%nat /\ v = VZ (if e_off =? 0 then e_rsv * 32 else 224)) \/
(off = 14 /\ w = 2%nat /\ v = VZ (if e_off =? 0 then 0 else e_off)) \/
(e_off <> 0 /\ off = 16 + 16 * e_off - 4 /\ w = 1%nat /\ v = VZ 0) \/
(e_off <> 0 /\ off = 16 + 16 * e_off - 3 /\ w = 1%nat /\ v = VZ (32 * e_rsv)) \/
(e_off <> 0 /\ off = 16 + 16 * e_off - 2 /\ w = 2%nat /\ v = VZ e_off) \/
(off = len - 4 /\ w = 1%nat /\ v = VZ 0) \/
(0 < e_reserved /\ off = 16 + 16 * e_off + n /\ w = 1%nat /\ v = VZ 0) \/
(5 <= e_reserved /\ off = len - 8 /\ w = 4%nat /\ v = VZ e_reserved) \/
(5 <= e_reserved /\ off = len - 9 /\ w = 1%nat /\ v = VZ 0))).
Lemma newc_cases : forall c, In c (new_cells ++ group_tail_cells am6) -> newc_spec c.
Proof.
intros c Hc. pose proof maplen_facts as (Hml & Hml2). pose proof e_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
assert (RSV : rsv_code am6 e_fr = e_rsv).
{ unfold rsv_code, e_rsv, e_reserved. rewrite stride_am6. cbn [fr_off fr_n e_fr]. reflexivity. }
assert (H16 : hdr_off16 am6 0 e_fr = e_off).
{ unfold hdr_off16. rewrite stride_am6, Z.mul_0_r. cbn [fr_off e_fr]. reflexivity. }
assert (RO : reserved_of am6 e_fr = e_reserved).
{ unfold reserved_of, e_reserved. rewrite stride_am6. cbn [fr_off fr_n e_fr]. reflexivity. }
assert (GE : group_extent am6 = len - IB).
{ unfold group_extent. rewrite stride_am6. change (am_last am6) with 0. rewrite F8. unfold UNIT, IB. lia. }
unfold new_cells in Hc. cbn [In app] in Hc. rewrite !in_app_iff in Hc.
destruct Hc as [<- | [[Hc | Hc] | Hc]].
- left. reflexivity.
-
right. left. cbn [meta_slot_cells In optr am_prev am_next am_mem am_avail am_freed am6 am4 direct_am upd_slot am_set_slots] in Hc.
rewrite (meta_bits_enc am6) in Hc. change (am_last am6) with 0 in Hc. change (am_sc am6) with 63 in Hc. change (am_maplen am6) with maplen in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
(eexists _, _, _; split; [reflexivity|]); unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits; tauto.
-
right. right. unfold group_cells in Hc.
change (am_mem am6) with (SP (r0 A) 0) in Hc. change (am_maplen am6) with maplen in Hc.
change (am_aidx am6) with 0 in Hc. change (am_last am6) with 0 in Hc.
change (zseq 0 (0 + 1)) with [0] in Hc. cbn [flat_map app] in Hc. rewrite app_nil_r in Hc.
rewrite (proj2 (Z.eqb_neq maplen 0)) in Hc by lia.
unfold slot_cells, slot_start in Hc. rewrite !stride_am6 in Hc. change (nth_slot am6 0) with (mkSlot (Some e_hdr) (Some e_fr)) in Hc.
change (am_mem am6) with (SP (r0 A) 0) in Hc.
cbn [ss_hdr ss_fr fr_off e_fr padd app In] in Hc. fold e_fr in Hc. rewrite ?RSV, ?H16 in Hc.
unfold e_hdr in Hc.
destruct (Z.eqb_spec e_off 0) as [E0|E0].
+ cbn [app In] in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; (eexists _, _, _; split; [reflexivity|]); (split; [reflexivity|]); cbn [poff]; unfold UNIT;
first [left; split; [lia|auto] | right; left; split; [lia|auto] | right; right; left; split; [lia|auto]
| right; right; right; left; split; [lia|auto] | right; right; right; right; left; split; [lia|auto]].
+ cbn [app In] in Hc. change (hdr_byte3 am6 0 e_fr) with (0 + 32 * rsv_code am6 e_fr) in Hc. rewrite RSV in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; (eexists _, _, _; split; [reflexivity|]); (split; [reflexivity|]); cbn [poff]; unfold UNIT.
* left. split; [lia|auto].
* right; left. split; [lia|auto].
* right; right; left. split; [lia|auto].
* right; right; right; left. split; [lia|auto].
* right; right; right; right; left. split; [lia|auto].
* do 5 right; left. split; [exact E0|]. split; [lia|auto].
* do 6 right; left. split; [exact E0|]. split; [lia|]. split; reflexivity.
* do 7 right; left. split; [exact E0|]. split; [lia|auto].
-
right. right. unfold group_tail_cells in Hc. rewrite GE in Hc. change (am_mem am6) with (SP (r0 A) 0) in Hc. change (am_last am6) with 0 in Hc.
change (zseq 0 (0 + 1)) with [0] in Hc. cbn [flat_map app] in Hc. rewrite app_nil_r in Hc.
unfold frame_tail_cells in Hc. change (nth_slot am6 0) with (mkSlot (Some e_hdr) (Some e_fr)) in Hc. cbn [ss_fr fr_kind e_fr] in Hc. fold e_fr in Hc.
rewrite RO in Hc. unfold frame_ptr, slot_end in Hc. unfold slot_start in Hc. rewrite !stride_am6 in Hc. change (am_mem am6) with (SP (r0 A) 0) in Hc.
cbn [fr_off fr_n e_fr padd In app] in Hc. rewrite in_app_iff in Hc.
destruct Hc as [<- | [Hc | Hc]].
+ eexists _, _, _. split; [reflexivity|]. split; [reflexivity|]. cbn [poff]. do 8 right; left. unfold IB. split; [lia|auto].
+ destruct (Z.ltb_spec 0 e_reserved); [|destruct Hc]. destruct Hc as [<-|[]].
eexists _, _, _. split; [reflexivity|]. split; [reflexivity|]. cbn [poff]. do 9 right; left. split; [assumption|]. unfold UNIT. split; [lia|auto].
+ destruct (Z.leb_spec 5 e_reserved); [|destruct Hc]. destruct Hc as [<-|[<-|[]]].
* eexists _, _, _. split; [reflexivity|]. split; [reflexivity|]. cbn [poff]. do 10 right; left. split; [assumption|]. rewrite F8. unfold UNIT, IB. split; [lia|auto].
* eexists _, _, _. split; [reflexivity|]. split; [reflexivity|]. cbn [poff]. do 11 right. split; [assumption|]. rewrite F8. unfold UNIT, IB. split; [lia|auto].
Qed.
Lemma bounded_A6 : bounded A3 -> bounded A6.
Proof. pose proof A6_fields as (_ & E2 & _ & E4 & E5 & _). unfold bounded, usage_of. rewrite E2, E4, E5. tauto. Qed.
Lemma ama_A6 : ama_ok A3 -> ama_ok A6.
Proof. pose proof A6_fields as (_ & E2 & E3 & _ & _ & E6 & _). unfold ama_ok. rewrite E2, E3, E6. tauto. Qed.
End u.
End i.
End b.
