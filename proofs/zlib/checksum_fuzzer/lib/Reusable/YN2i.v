(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YP09 YK0v YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0z YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN2b YN2c.
From Stdlib Require Import List.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma w64_u64 : forall w : word, Z_to_bv 64 (bv_unsigned w) = w.
Proof. intros w. apply Z_to_bv_bv_unsigned. Qed.
Lemma u64_w64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Lemma iv_subtract_disjoint : forall a sz lo hi,
lo <= hi -> 0 < bv_unsigned sz -> (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) ->
iv_subtract a sz lo hi = [(a, sz)].
Proof.
intros a sz lo hi Hle Hnz Hd. pose proof (u64_range a). pose proof (u64_range sz).
unfold iv_subtract. cbv zeta. destruct Hd as [Hd|Hd].
- replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
replace (hi <? bv_unsigned a + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia).
cbn [app]. rewrite Z.min_l by lia. rewrite w64_u64. reflexivity.
- replace (bv_unsigned a <? lo) with false by (symmetry; apply Z.ltb_ge; lia).
replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
rewrite !w64_u64. reflexivity.
Qed.
Lemma In_maps_subtract : forall l lo hi e,
0 <= lo <= hi -> In e (maps_subtract l lo hi) ->
exists e0, In e0 l /\ (iv_lo e0 + iv_len e0 <= 2 ^ 64 ->
iv_lo e0 <= iv_lo e /\ iv_lo e + iv_len e <= iv_lo e0 + iv_len e0 /\
(iv_lo e + iv_len e <= lo \/ hi <= iv_lo e) /\ (0 < iv_len e0 -> 0 < iv_len e)).
Proof.
induction l as [|[a sz] l IH]; intros lo hi e Hle Hin; [destruct Hin|].
cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
- exists (a, sz). split; [left; reflexivity|]. pose proof (u64_range a). pose proof (u64_range sz).
unfold iv_lo, iv_len. cbn [fst snd]. intros Hnw.
unfold iv_subtract in Hin. cbv zeta in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ destruct (bv_unsigned a <? lo) eqn:E1; [|destruct Hin]. apply Z.ltb_lt in E1. destruct Hin as [<-|[]].
cbn [fst snd]. rewrite u64_w64 by lia. lia.
+ destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2; [|destruct Hin]. apply Z.ltb_lt in E2. destruct Hin as [<-|[]].
cbn [fst snd]. rewrite !u64_w64 by lia. lia.
- destruct (IH lo hi e Hle Hin) as (e0 & H0 & H1). exists e0. split; [right; exact H0 | exact H1].
Qed.
Lemma maps_subtract_keep : forall l lo hi e,
lo <= hi -> In e l -> 0 < iv_len e -> (iv_lo e + iv_len e <= lo \/ hi <= iv_lo e) -> In e (maps_subtract l lo hi).
Proof.
induction l as [|[a sz] l IH]; intros lo hi e Hle Hin Hnz Hd; [destruct Hin|].
cbn [maps_subtract]. apply in_app_iff. destruct Hin as [<-|Hin].
- left. unfold iv_lo, iv_len in *. cbn [fst snd] in *. rewrite (iv_subtract_disjoint a sz lo hi Hle Hnz Hd). left. reflexivity.
- right. apply IH; assumption.
Qed.
Lemma length_iv_subtract_prefix : forall a sz lo hi,
lo = bv_unsigned a -> lo < hi -> hi < bv_unsigned a + bv_unsigned sz ->
iv_subtract a sz lo hi = [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))].
Proof.
intros a sz lo hi Hlo Hlt Hhi. unfold iv_subtract. cbv zeta.
replace (bv_unsigned a <? lo) with false by (symmetry; apply Z.ltb_ge; lia).
replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
cbn [app]. rewrite Z.max_r by lia. reflexivity.
Qed.
Lemma map_contains_In : forall l lo n,
map_contains l lo n = true <-> exists e, In e l /\ iv_lo e <= bv_unsigned lo /\ bv_unsigned lo + bv_unsigned n <= iv_lo e + iv_len e.
Proof.
intros l lo n. unfold map_contains. rewrite existsb_exists. unfold iv_lo, iv_len. split.
- intros (e & He & Hb). apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. exists e. auto.
- intros (e & He & H1 & H2). exists e. split; [exact He|]. apply andb_true_intro. split; apply Z.leb_le; assumption.
Qed.
Lemma map_contains_subtract : forall l lo n clo chi,
0 <= clo <= chi -> map_contains l lo n = true -> 0 < bv_unsigned n ->
(bv_unsigned lo + bv_unsigned n <= clo \/ chi <= bv_unsigned lo) ->
map_contains (maps_subtract l clo chi) lo n = true.
Proof.
intros l lo n clo chi Hle Hc Hn Hd. apply map_contains_In in Hc as (e & He & H1 & H2). apply map_contains_In.
pose proof (u64_range (fst e)). pose proof (u64_range (snd e)). pose proof (u64_range lo).
revert He. induction l as [|[a sz] l IH]; intros He; [destruct He|].
cbn [maps_subtract]. destruct He as [<- | He].
- unfold iv_lo, iv_len in *. cbn [fst snd] in *. unfold iv_subtract. cbv zeta. destruct Hd as [Hd|Hd].
+ exists (a, Z_to_bv 64 (Z.min (bv_unsigned sz) (clo - bv_unsigned a))). split.
* apply in_app_iff. left. replace (bv_unsigned a <? clo) with true by (symmetry; apply Z.ltb_lt; lia). left. reflexivity.
* cbn [fst snd]. rewrite u64_w64 by lia. lia.
+ exists (Z_to_bv 64 (Z.max (bv_unsigned a) chi), Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) chi)). split.
* apply in_app_iff. left. apply in_app_iff. right.
replace (chi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia). left. reflexivity.
* cbn [fst snd]. rewrite !u64_w64 by lia. lia.
- destruct (IH He) as (e' & He' & H'). exists e'. split; [apply in_app_iff; right; exact He' | exact H'].
Qed.
Lemma map_contains_cons' : forall e l lo n, map_contains l lo n = true -> map_contains (e :: l) lo n = true.
Proof. intros e l lo n H. unfold map_contains in *. cbn. rewrite H. apply orb_true_r. Qed.
Lemma map_contains_head : forall a sz l lo n,
bv_unsigned a <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= bv_unsigned a + bv_unsigned sz ->
map_contains ((a, sz) :: l) lo n = true.
Proof.
intros a sz l lo n H1 H2. apply map_contains_In. exists (a, sz). split; [left; reflexivity|]. unfold iv_lo, iv_len. cbn. lia.
Qed.
Lemma live_bytes_maps_subtract_le : forall l lo hi, lo <= hi -> State.live_bytes (maps_subtract l lo hi) <= State.live_bytes l.
Proof. intros. apply maps_subtract_le. assumption. Qed.
Lemma length_maps_subtract_keep : forall l lo hi,
lo <= hi -> (forall e, In e l -> 0 < iv_len e /\ (iv_lo e + iv_len e <= lo \/ hi <= iv_lo e)) ->
maps_subtract l lo hi = l.
Proof.
induction l as [|[a sz] l IH]; intros lo hi Hle H; [reflexivity|]. cbn [maps_subtract].
destruct (H (a, sz) (or_introl eq_refl)) as [Hnz Hd]. unfold iv_lo, iv_len in Hnz, Hd. cbn [fst snd] in Hnz, Hd.
rewrite (iv_subtract_disjoint a sz lo hi Hle Hnz Hd). cbn [app]. f_equal. apply IH; [exact Hle|]. intros e He. apply H. right. exact He.
Qed.
Lemma live_bytes_app_region : forall l rg,
fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 (l ++ [rg])
= fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 l + (if rg_live rg then rg_len rg else 0).
Proof. induction l as [|x l IH]; intros rg; cbn; [destruct (rg_live rg); lia|]. rewrite IH. destruct (rg_live x); lia. Qed.
Lemma live_bytes_new : forall s s' rg, st_regions s' = st_regions s ++ [rg] -> rg_live rg = true -> live_bytes s' = live_bytes s + rg_len rg.
Proof. intros s s' rg E Hl. unfold live_bytes. rewrite E, live_bytes_app_region, Hl. reflexivity. Qed.
Lemma nslots_new : forall s s' rg, st_regions s' = st_regions s ++ [rg] -> nslots s' = nslots s + region_slots rg.
Proof.
intros s s' rg E. unfold nslots. rewrite E. clear E.
induction (st_regions s) as [|x l IH]; cbn -[region_slots Z.add]; [lia|]. rewrite IH. lia.
Qed.
Lemma fold_live_lupd : forall l r rg rg', nth_error l r = Some rg ->
fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 (lupd l r rg')
= fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 l
- (if rg_live rg then rg_len rg else 0) + (if rg_live rg' then rg_len rg' else 0).
Proof.
induction l as [|x l IH]; intros [|r] rg rg' H; cbn in H; try discriminate; cbn.
- injection H as ->. destruct (rg_live rg), (rg_live rg'); lia.
- rewrite (IH r rg rg' H). destruct (rg_live x); lia.
Qed.
Lemma live_bytes_upd : forall s s' r rg rg', st_regions s' = lupd (st_regions s) r rg' -> region_of s r = Some rg ->
rg_live rg = true -> rg_live rg' = true -> live_bytes s' = live_bytes s - rg_len rg + rg_len rg'.
Proof. intros s s' r rg rg' E Hr Hl Hl'. unfold live_bytes. rewrite E, (fold_live_lupd _ r rg rg' Hr), Hl, Hl'. lia. Qed.
Lemma fold_slots_lupd : forall l r rg rg', nth_error l r = Some rg ->
fold_right (fun rg acc => region_slots rg + acc) 0 (lupd l r rg')
= fold_right (fun rg acc => region_slots rg + acc) 0 l - region_slots rg + region_slots rg'.
Proof.
induction l as [|x l IH]; intros [|r] rg rg' H; cbn -[region_slots] in *; try discriminate.
- injection H as ->. lia.
- rewrite (IH r rg rg' H). lia.
Qed.
Lemma nslots_upd : forall s s' r rg rg', st_regions s' = lupd (st_regions s) r rg' -> region_of s r = Some rg ->
nslots s' = nslots s - region_slots rg + region_slots rg'.
Proof. intros s s' r rg rg' E Hr. unfold nslots. rewrite E, (fold_slots_lupd _ r rg rg' Hr). reflexivity. Qed.
Lemma region_of_new : forall s s' rg k, st_regions s' = st_regions s ++ [rg] ->
region_of s' k = if (k <? length (st_regions s))%nat then region_of s k
else if Nat.eqb k (length (st_regions s)) then Some rg else None.
Proof.
intros s s' rg k E. unfold region_of. rewrite E.
destruct (Nat.ltb_spec k (length (st_regions s))).
- apply nth_error_app1. exact H.
- rewrite nth_error_app2 by lia. destruct (Nat.eqb_spec k (length (st_regions s))).
+ subst. rewrite Nat.sub_diag. reflexivity.
+ destruct (k - length (st_regions s))%nat as [|m] eqn:E2; [lia|]. cbn. destruct m; reflexivity.
Qed.
Lemma region_of_updk : forall s s' r rg' k, st_regions s' = lupd (st_regions s) r rg' ->
region_of s' k = if (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool then Some rg' else region_of s k.
Proof. intros s s' r rg' k E. unfold region_of. rewrite E. apply nth_error_lupd. Qed.
Lemma vm_backing_used_le_maps : forall md, m_vm_lazy md = [] -> m_vm_materialized md = [] ->
vm_backing_used md <= State.live_bytes (vm_maps (m_vmmaps md)).
Proof.
intros md Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul].
unfold vm_backed_maps. pose proof (maps_subtract_all_le (vm_noaccess (m_vmmaps md)) (vm_maps (m_vmmaps md))). lia.
Qed.
Section Ev.
Variable B : malloc_syms.
Variables (L : layout) (A : astate) (md : Model).
Hypothesis LG : ledger_ok B L A md.
Hypothesis LX : ledger_x L A md.
Hypothesis NN : forall k rg, region_of A k = Some rg -> 0 <= rg_len rg.
Hypothesis MD : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Let N := length (st_regions A).
Lemma ledger_same : forall A' md',
st_regions A' = st_regions A -> st_brk A' = st_brk A ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_vm_materialized md' = m_vm_materialized md ->
ledger_ok B L A' md' /\ ledger_x L A' md'.
Proof.
intros A' md' ER EB EV EL EM. split.
- assert (VB : vm_backing_used md' = vm_backing_used md) by (apply vm_backing_used_ext; assumption).
split; unfold region_of, live_bytes, nslots; rewrite ?ER, ?EB, ?EV, ?VB; try apply LG.
- eapply ledger_x_same_regions; [exact LX | exact ER | rewrite EV; reflexivity | rewrite EV; reflexivity].
Qed.
Lemma ledger_brk_dead : forall A' md',
st_regions A' = st_regions A -> st_brk A' = BrkDead ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_vm_materialized md' = m_vm_materialized md ->
ledger_ok B L A' md' /\ ledger_x L A' md'.
Proof.
intros A' md' ER EB EV EL EM. split.
- assert (VB : vm_backing_used md' = vm_backing_used md) by (apply vm_backing_used_ext; assumption).
split; unfold region_of, live_bytes, nslots; rewrite ?ER, ?EB, ?EV, ?VB; try apply LG. exact I.
- eapply ledger_x_same_regions; [exact LX | exact ER | rewrite EV; reflexivity | rewrite EV; reflexivity].
Qed.
Definition Lset (v : Z) : layout := Layout (ly_ctx L) (fun k => if Nat.eqb k N then v else ly_reg L k) (ly_brk0 L) (ly_sec L).
Lemma Lset_old : forall v k rg, region_of A k = Some rg -> ly_reg (Lset v) k = ly_reg L k.
Proof. intros v k rg H. cbn. pose proof (region_of_lt _ _ _ H). fold N in H0. destruct (Nat.eqb_spec k N); [lia | reflexivity]. Qed.
Lemma Lset_new : forall v, ly_reg (Lset v) N = v.
Proof. intros v. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma Lset_lt : forall v k, (k < N)%nat -> ly_reg (Lset v) k = ly_reg L k.
Proof. intros v k H. cbn. destruct (Nat.eqb_spec k N); [lia | reflexivity]. Qed.
Lemma live_bytes_nonneg' : 0 <= live_bytes A.
Proof.
unfold live_bytes. unfold region_of in NN.
assert (GG : forall l, (forall k rg, nth_error l k = Some rg -> 0 <= rg_len rg) ->
0 <= fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 l).
{ induction l as [|x l IH]; intros Hl; cbn; [lia|].
assert (0 <= rg_len x) by (apply (Hl 0%nat x); reflexivity).
assert (0 <= fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 l)
by (apply IH; intros k rg Hk; apply (Hl (S k) rg); exact Hk).
destruct (rg_live x); lia. }
apply GG. exact NN.
Qed.
Section d.
Variables (a : word) (n : Z).
Hypothesis Hn : 0 < n.
Hypothesis Ha0 : 0 < bv_unsigned a.
Hypothesis Han : bv_unsigned a + n <= 2 ^ 64.
Hypothesis RF : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a (Z_to_bv 64 n) = true.
Lemma n_u : bv_unsigned (Z_to_bv 64 n) = n.
Proof. pose proof (u64_range a). apply u64_w64. lia. Qed.
Lemma fresh_entry : forall e, In e (vm_maps (m_vmmaps md)) -> ranges_disjoint (bv_unsigned a, n) (iv_lo e, iv_len e).
Proof.
intros e He. destruct (lx_maps _ _ _ LX e He) as [P _].
pose proof (region_free_In _ a (Z_to_bv 64 n) e RF ltac:(apply in_app_iff; right; exact He) ltac:(rewrite n_u; lia) P) as D.
rewrite n_u in D. exact D.
Qed.
Lemma fresh_img : forall x, in_img B x -> ~ (bv_unsigned a <= x < bv_unsigned a + n).
Proof.
intros x [_ (sg & Hsg & Hx)] Hin. rewrite <- (lg_reserved _ _ _ _ LG) in Hsg.
pose proof (region_free_In _ a (Z_to_bv 64 n) sg RF ltac:(apply in_app_iff; left; exact Hsg) ltac:(rewrite n_u; lia) ltac:(lia)) as D.
rewrite n_u in D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma fresh_region : forall k rg x, region_of A k = Some rg -> rg_live rg = true ->
ly_reg L k + reg_lo rg <= x < ly_reg L k + rg_len rg -> ~ (bv_unsigned a <= x < bv_unsigned a + n).
Proof.
intros k rg x Hk Hl Hx Hin. destruct (lx_cov _ _ _ LX k rg x Hk Hl Hx) as (e & He & Hex).
pose proof (fresh_entry e He) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.
End d.
Lemma ledger_new_resv : forall A' (a : word) (n : Z),
0 < n -> n mod PGSZ = 0 -> place_ok (Z_to_bv 64 0) md a n = true ->
st_regions A' = st_regions A ++ [mkRegion RkMetaRes n [] true] -> st_brk A' = st_brk A ->
(forall r p, st_brk A = BrkCur r p -> (r < N)%nat) ->
ledger_ok B (Lset (bv_unsigned a)) A' (mmap_none_model a (Z_to_bv 64 n) md) /\
ledger_x (Lset (bv_unsigned a)) A' (mmap_none_model a (Z_to_bv 64 n) md).
Proof.
intros A' a n Hn Hpg PL ER EB BR.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range a) as Ua.
unfold place_ok in PL. apply andb_prop in PL as [PL RF]. apply andb_prop in PL as [PL Htop].
apply andb_prop in PL as [Hal Hpos]. apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
unfold page_size in Hal.
assert (Hceil : bv_unsigned a + n <= alloc_ceiling).
{ apply (YM05.grant_below_ceil _ _ (lg_ceil _ _ _ _ LG)); [| exact Htop].
rewrite Z.add_mod, Hal by lia. unfold PGSZ in Hpg. rewrite Hpg. reflexivity. }
assert (NU : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_w64; lia).
assert (VM : vm_maps (m_vmmaps (mmap_none_model a (Z_to_bv 64 n) md)) = (a, Z_to_bv 64 n) :: vm_maps (m_vmmaps md)) by reflexivity.
assert (VN : vm_noaccess (m_vmmaps (mmap_none_model a (Z_to_bv 64 n) md)) = (a, Z_to_bv 64 n) :: vm_noaccess (m_vmmaps md)) by reflexivity.
pose proof (fun k => region_of_new A A' _ k ER) as RO. cbn beta in RO. fold N in RO.
pose proof (live_bytes_new A A' _ ER eq_refl) as LB. cbn [rg_len] in LB.
pose proof (nslots_new A A' _ ER) as NS. unfold region_slots in NS. cbn [rg_live rg_kind] in NS.
pose proof live_bytes_nonneg' as LNN.
pose proof (fresh_region a n Hn Hpos ltac:(lia) RF) as FRG. pose proof (fresh_entry a n Hn Hpos ltac:(lia) RF) as FE. pose proof (fresh_img a n Hn Hpos ltac:(lia) RF) as FI.
split.
- split; rewrite ?VM, ?VN.
+ exact (lg_reserved _ _ _ _ LG).
+ exact (lg_limit _ _ _ _ LG).
+ intros k rg Hk Hl Hkind. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
* right. rewrite (Lset_lt _ k H). exact (lg_maps _ _ _ _ LG k rg Hk Hl Hkind).
* destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. subst k. left. unfold w64. rewrite Lset_new, w64_u64. reflexivity.
+ intros k rg off Hk Hl Hkind Ho1 Ho2 Ho3 Hrw. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
* unfold w64 in *. rewrite (Lset_lt _ k H). destruct (lg_noaccess _ _ _ _ LG k rg off Hk Hl Hkind Ho1 Ho2 Ho3 Hrw) as [N1 N2].
split; apply map_contains_cons'; assumption.
* destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. subst k. rewrite Lset_new. cbn [rg_len] in Ho2.
assert (E2 : bv_unsigned (w64 PGSZ) = 4096) by reflexivity. unfold PGSZ in *.
assert (E1 : bv_unsigned (w64 (bv_unsigned a + off)) = bv_unsigned a + off) by (unfold w64; apply u64_w64; lia).
split; apply map_contains_head; rewrite ?E1, ?E2, ?NU; lia.
+ exact (lg_brk0 _ _ _ _ LG).
+ rewrite EB. pose proof (lg_brk _ _ _ _ LG) as HB. destruct (st_brk A) as [| |r p] eqn:Ebk; try exact HB.
rewrite (Lset_lt _ r (BR r p eq_refl)). exact HB.
+ intros k rg Hk Hl. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
* rewrite (Lset_lt _ k H). exact (lg_placed _ _ _ _ LG k rg Hk Hl).
* destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. subst k. rewrite Lset_new. cbn [rg_len].
split; [exact Hal|]. split; [apply Z.mod_divide in Hal; [destruct Hal as [q Hq]; lia | lia]|].
split; [exact Hceil|]. intros x Hx Himg. exact (FI x Himg Hx).
+ cbn [length]. rewrite NS. pose proof (lg_count _ _ _ _ LG). lia.
+ rewrite LB. constructor.
* cbn [snd]. rewrite NU. lia.
* apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (lg_sizes _ _ _ _ LG) e He). cbn beta in *. lia.
+ rewrite LB. destruct MD as (_ & ML & MM).
pose proof (vm_backing_used_le_maps (mmap_none_model a (Z_to_bv 64 n) md) ltac:(rewrite mmap_none_model_lazy; exact ML) MM) as VB.
rewrite VM in VB. cbn [State.live_bytes] in VB. rewrite NU in VB. pose proof (lx_lb _ _ _ LX). lia.
+   exact (lg_ceil _ _ _ _ LG).
- split; rewrite ?VM.
+ intros k rg x Hk Hl Hx. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
* rewrite (Lset_lt _ k H) in Hx. destruct (lx_cov _ _ _ LX k rg x Hk Hl Hx) as (e & He & Hex). exists e. split; [right; exact He | exact Hex].
* destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. subst k. rewrite Lset_new in Hx. cbn [reg_lo rg_kind rg_len] in Hx.
exists (a, Z_to_bv 64 n). split; [left; reflexivity|]. unfold iv_lo, iv_len. cbn [fst snd]. rewrite NU. lia.
+ intros e [<- | He]; [| exact (lx_maps _ _ _ LX e He)]. unfold iv_lo, iv_len; cbn [fst snd]. rewrite NU. lia.
+ intros e1 e2 [<- | H1] [<- | H2].
* left. reflexivity.
* right. pose proof (FE e2 H2) as D. unfold iv_lo, iv_len in *; cbn [fst snd]. rewrite NU. exact D.
* right. pose proof (FE e1 H1) as D. unfold ranges_disjoint, iv_lo, iv_len in *; cbn [fst snd] in *. rewrite NU. lia.
* exact (lx_disj _ _ _ LX e1 e2 H1 H2).
+ intros k1 k2 rg1 rg2 Hne H1 H2 Hl1 Hl2 N1 N2. rewrite RO in H1, H2.
destruct (Nat.ltb_spec k1 N); destruct (Nat.ltb_spec k2 N).
* rewrite (Lset_lt _ k1 H), (Lset_lt _ k2 H0). exact (lx_regs _ _ _ LX k1 k2 rg1 rg2 Hne H1 H2 Hl1 Hl2 N1 N2).
* destruct (Nat.eqb_spec k2 N); [|discriminate]. injection H2 as <-. subst k2. rewrite (Lset_lt _ k1 H), Lset_new.
cbn [reg_lo rg_kind rg_len] in *. unfold ranges_disjoint; cbn [fst snd].
pose proof (FRG k1 rg1 (ly_reg L k1 + reg_lo rg1) H1 Hl1 ltac:(lia)).
pose proof (FRG k1 rg1 (bv_unsigned a) H1 Hl1). lia.
* destruct (Nat.eqb_spec k1 N); [|discriminate]. injection H1 as <-. subst k1. rewrite (Lset_lt _ k2 H0), Lset_new.
cbn [reg_lo rg_kind rg_len] in *. unfold ranges_disjoint; cbn [fst snd].
pose proof (FRG k2 rg2 (ly_reg L k2 + reg_lo rg2) H2 Hl2 ltac:(lia)).
pose proof (FRG k2 rg2 (bv_unsigned a) H2 Hl2). lia.
* destruct (Nat.eqb_spec k1 N); [|discriminate]. destruct (Nat.eqb_spec k2 N); [|discriminate]. exfalso. apply Hne. lia.
+ intros e [<- | He].
* exists N, (mkRegion RkMetaRes n [] true). rewrite RO, Nat.ltb_irrefl, Nat.eqb_refl. split; [reflexivity|]. split; [reflexivity|].
rewrite Lset_new. unfold iv_lo, iv_len; cbn [fst snd rg_len]. rewrite NU. lia.
* destruct (lx_in _ _ _ LX e He) as (k & rg & Hk & Hl & G1 & G2). exists k, rg.
pose proof (region_of_lt _ _ _ Hk) as HkN. fold N in HkN.
rewrite RO. rewrite (proj2 (Nat.ltb_lt k N) HkN). rewrite (Lset_lt _ k HkN). auto.
+ rewrite LB. cbn [State.live_bytes]. rewrite NU. pose proof (lx_lb _ _ _ LX). lia.
+
assert (RK : forall E k rg, rg_kind rg = RkMap ->
(region_of A k = Some rg -> rg_live rg = true -> ranges_disjoint (iv_lo E, iv_len E) (ly_reg L k, rg_len rg)) ->
region_of A' k = Some rg -> rg_live rg = true -> ranges_disjoint (iv_lo E, iv_len E) (ly_reg (Lset (bv_unsigned a)) k, rg_len rg)).
{ intros E k rg Hkd H Hk Hl. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
- rewrite (Lset_lt _ k H0). exact (H Hk Hl).
- destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. discriminate. }
rewrite VN. intros e [<- | He].
* exists (a, Z_to_bv 64 n). split; [left; reflexivity|]. split; [lia|]. split; [lia|].
intros k rg Hk Hl Hkd Hp. apply (RK _ k rg Hkd); [| exact Hk | exact Hl]. intros Hk0 Hl0.
unfold ranges_disjoint, iv_lo, iv_len; cbn [fst snd]. rewrite NU.
pose proof (FRG k rg (ly_reg L k) Hk0 Hl0 ltac:(unfold reg_lo; rewrite Hkd; lia)).
pose proof (FRG k rg (bv_unsigned a) Hk0 Hl0) as F2. unfold reg_lo in F2. rewrite Hkd in F2. cbn in F2. lia.
* destruct (lx_noacc _ _ _ LX e He) as (E & HE & G1 & G2 & HR). exists E. split; [right; exact HE|].
split; [exact G1|]. split; [exact G2|]. intros k rg Hk Hl Hkd Hp. apply (RK _ k rg Hkd); [| exact Hk | exact Hl].
intros Hk0 Hl0. exact (HR k rg Hk0 Hl0 Hkd Hp).
Qed.
Lemma ledger_x_iso : forall A' md',
(forall k rg', region_of A' k = Some rg' -> exists rg, region_of A k = Some rg /\
rg_kind rg = rg_kind rg' /\ rg_len rg = rg_len rg' /\ rg_live rg = rg_live rg') ->
(forall k rg, region_of A k = Some rg -> exists rg', region_of A' k = Some rg' /\
rg_kind rg = rg_kind rg' /\ rg_len rg = rg_len rg' /\ rg_live rg = rg_live rg') ->
live_bytes A' = live_bytes A ->
vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) ->
(forall e, In e (vm_noaccess (m_vmmaps md')) ->
exists e0, In e0 (vm_noaccess (m_vmmaps md)) /\ iv_lo e0 <= iv_lo e /\ iv_lo e + iv_len e <= iv_lo e0 + iv_len e0) ->
ledger_x L A' md'.
Proof.
intros A' md' ISO ISO' ELB EV EN. split; rewrite ?EV, ?ELB.
- intros k rg' x Hk Hl Hx. destruct (ISO k rg' Hk) as (rg & Hr & K1 & K2 & K3).
apply (lx_cov _ _ _ LX k rg x Hr); [congruence|]. unfold reg_lo in *. rewrite K1, K2. exact Hx.
- exact (lx_maps _ _ _ LX).
- exact (lx_disj _ _ _ LX).
- intros k1 k2 rg1' rg2' Hne H1 H2 L1 L2 N1 N2.
destruct (ISO k1 rg1' H1) as (rg1 & R1 & K11 & K12 & K13). destruct (ISO k2 rg2' H2) as (rg2 & R2 & K21 & K22 & K23).
unfold reg_lo in *. rewrite <- K11, <- K12, <- K21, <- K22 in *.
apply (lx_regs _ _ _ LX k1 k2 rg1 rg2 Hne R1 R2); try congruence; unfold reg_lo; assumption.
- intros e He. destruct (lx_in _ _ _ LX e He) as (k & rg & Hk & Hl & G1 & G2).
destruct (ISO' k rg Hk) as (rg' & Hr' & K1 & K2 & K3). exists k, rg'. rewrite <- K2, <- K3. auto.
- exact (lx_lb _ _ _ LX).
- intros e He. destruct (EN e He) as (e0 & He0 & S1 & S2).
destruct (lx_noacc _ _ _ LX e0 He0) as (E & HE & G1 & G2 & HR). exists E. split; [exact HE|].
split; [lia|]. split; [lia|]. intros k rg' Hk Hl Hkd Hp.
destruct (ISO k rg' Hk) as (rg & Hr & K1 & K2 & K3). rewrite <- K2. apply (HR k rg Hr); try congruence; lia.
Qed.
Lemma ledger_mprotect : forall A' r len rw off,
region_of A r = Some (mkRegion RkMetaRes len rw true) ->
0 <= off -> off + PGSZ <= len -> off mod PGSZ = 0 -> ~ In off rw ->
st_regions A' = lupd (st_regions A) r (mkRegion RkMetaRes len (rw ++ [off]) true) -> st_brk A' = st_brk A ->
ledger_ok B L A' (mprotect_model (w64 (ly_reg L r + off)) (w64 PGSZ) md) /\
ledger_x L A' (mprotect_model (w64 (ly_reg L r + off)) (w64 PGSZ) md).
Proof.
intros A' r len rw off Hr Ho1 Ho2 Ho3 Hrw ER EB.
pose proof (proj1 alloc_ceiling_val) as AC.
set (md' := mprotect_model _ _ md).
pose proof (lg_placed _ _ _ _ LG r _ Hr eq_refl) as (Pal & Plo & Phi & Pimg). cbn [rg_len] in Phi.
assert (EP : bv_unsigned (w64 (ly_reg L r + off)) = ly_reg L r + off) by (unfold w64; apply u64_w64; unfold PGSZ in *; lia).
assert (E4 : bv_unsigned (w64 PGSZ) = 4096) by reflexivity.
assert (VM : vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md)) by reflexivity.
assert (VN : vm_noaccess (m_vmmaps md') = maps_subtract (vm_noaccess (m_vmmaps md)) (ly_reg L r + off) (ly_reg L r + off + 4096)).
{ unfold md', mprotect_model, mprotect_model_next. cbn -[maps_subtract Z.add bv_unsigned w64]. rewrite EP, E4. reflexivity. }
pose proof (fun k => region_of_updk A A' r _ k ER) as RO. cbn beta in RO.
pose proof (region_of_lt _ _ _ Hr) as HrN.
assert (ROr : region_of A' r = Some (mkRegion RkMetaRes len (rw ++ [off]) true)).
{ rewrite RO, Nat.eqb_refl, (proj2 (Nat.ltb_lt _ _) HrN). reflexivity. }
assert (ROo : forall k, k <> r -> region_of A' k = region_of A k).
{ intros k Hk. rewrite RO. rewrite (proj2 (Nat.eqb_neq _ _) Hk). reflexivity. }
assert (ISO : forall k rg', region_of A' k = Some rg' -> exists rg, region_of A k = Some rg /\
rg_kind rg = rg_kind rg' /\ rg_len rg = rg_len rg' /\ rg_live rg = rg_live rg').
{ intros k rg' Hk. destruct (Nat.eq_dec k r) as [->|Hne].
- rewrite ROr in Hk. injection Hk as <-. eexists. split; [exact Hr|]. cbn. auto.
- rewrite (ROo k Hne) in Hk. exists rg'. auto. }
assert (ISO' : forall k rg, region_of A k = Some rg -> exists rg', region_of A' k = Some rg' /\
rg_kind rg = rg_kind rg' /\ rg_len rg = rg_len rg' /\ rg_live rg = rg_live rg').
{ intros k rg Hk. destruct (Nat.eq_dec k r) as [->|Hne].
- rewrite Hr in Hk. injection Hk as <-. eexists. split; [exact ROr|]. cbn. auto.
- exists rg. rewrite (ROo k Hne). auto. }
assert (ELB : live_bytes A' = live_bytes A).
{ rewrite (live_bytes_upd A A' r _ _ ER Hr eq_refl eq_refl). cbn. lia. }
assert (ENS : nslots A' = nslots A).
{ rewrite (nslots_upd A A' r _ _ ER Hr). unfold region_slots. cbn. lia. }
split.
- split; rewrite ?VM, ?VN, ?ELB, ?ENS, ?EB.
+ exact (lg_reserved _ _ _ _ LG).
+ exact (lg_limit _ _ _ _ LG).
+ intros k rg' Hk Hl Hkind. destruct (ISO k rg' Hk) as (rg & Hk0 & K1 & K2 & K3).
rewrite <- K2. apply (lg_maps _ _ _ _ LG k rg Hk0); congruence.
+ intros k rg' off' Hk Hl Hkind Ha1 Ha2 Ha3 Hnin.
destruct (Nat.eq_dec k r) as [->|Hne].
* rewrite ROr in Hk. injection Hk as <-. cbn [rg_len rg_rw] in *.
assert (Hno : ~ In off' rw /\ off' <> off).
{ split; [intros Hin; apply Hnin; apply in_app_iff; left; exact Hin | intros ->; apply Hnin; apply in_app_iff; right; left; reflexivity]. }
destruct Hno as [Hno Hne'].
destruct (lg_noaccess _ _ _ _ LG r _ off' Hr eq_refl eq_refl Ha1 Ha2 Ha3 Hno) as [N1 N2]. split; [|exact N2].
apply map_contains_subtract; [unfold PGSZ in *; lia | exact N1 | rewrite E4; lia |].
unfold w64 in *. rewrite u64_w64 by (unfold PGSZ in *; lia). rewrite E4.
unfold PGSZ in *. apply Z.mod_divide in Ho3; [|lia]. apply Z.mod_divide in Ha3; [|lia].
destruct Ho3 as [q Hq]. destruct Ha3 as [q' Hq']. assert (q <> q') by (intros ->; apply Hne'; lia). nia.
* rewrite (ROo k Hne) in Hk.
destruct (lg_noaccess _ _ _ _ LG k rg' off' Hk Hl Hkind Ha1 Ha2 Ha3 Hnin) as [N1 N2]. split; [|exact N2].
apply map_contains_subtract; [unfold PGSZ in *; lia | exact N1 | rewrite E4; lia |].
unfold w64 in *. pose proof (lg_placed _ _ _ _ LG k rg' Hk Hl) as (_ & Klo & Khi & _).
rewrite u64_w64 by (unfold PGSZ in *; lia). rewrite E4.
pose proof (lx_regs _ _ _ LX r k _ rg' ltac:(congruence) Hr Hk eq_refl Hl) as D.
unfold reg_lo, ranges_disjoint in D. rewrite Hkind in D. cbn [rg_kind rg_len fst snd] in D. unfold PGSZ in *. lia.
+ exact (lg_brk0 _ _ _ _ LG).
+ pose proof (lg_brk _ _ _ _ LG) as HB. exact HB.
+ intros k rg' Hk Hl. destruct (ISO k rg' Hk) as (rg & Hk0 & K1 & K2 & K3). rewrite <- K2. apply (lg_placed _ _ _ _ LG k rg Hk0). congruence.
+ exact (lg_count _ _ _ _ LG).
+ exact (lg_sizes _ _ _ _ LG).
+ destruct MD as (_ & ML & MM).
pose proof (vm_backing_used_le_maps md' ML MM) as VB. rewrite VM in VB. pose proof (lx_lb _ _ _ LX). lia.
+   exact (lg_ceil _ _ _ _ LG).
- apply (ledger_x_iso A' md' ISO ISO' ELB VM).
intros e He. rewrite VN in He. eapply In_maps_subtract_sub; [|exact He]. unfold PGSZ in *. lia.
Qed.
Lemma ledger_grow_brk : forall A' md' r p len rw,
let h := m_vmmaps md in let b := vm_brk h in
st_brk A = BrkCur r p -> region_of A r = Some (mkRegion RkBrk len rw true) -> len = PGSZ * p -> 2 <= p ->
bv_unsigned b + PGSZ <= alloc_ceiling ->
region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 PGSZ) = true ->
st_regions A' = lupd (st_regions A) r (mkRegion RkBrk (len + PGSZ) [] true) -> st_brk A' = BrkCur r (p + 1) ->
vm_maps (m_vmmaps md') = (b, w64 PGSZ) :: vm_maps h -> vm_noaccess (m_vmmaps md') = vm_noaccess h ->
vm_reserved (m_vmmaps md') = vm_reserved h -> vm_start_brk (m_vmmaps md') = vm_start_brk h ->
bv_unsigned (vm_brk (m_vmmaps md')) = bv_unsigned b + PGSZ -> vm_limit (m_vmmaps md') = vm_limit h ->
alloc_top (m_vmmaps md') = alloc_top h ->
m_vm_lazy md' = [] -> m_vm_materialized md' = [] ->
ledger_ok B L A' md' /\ ledger_x L A' md'.
Proof.
intros A' md' r p len rw h b Hbk Hr Hlen Hp Gceil Gfree ER EB VM VN VR VS VB VL VT ML' MM'.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range b) as Ub. subst h.
pose proof (lg_brk _ _ _ _ LG) as HB. rewrite Hbk in HB. destruct HB as [HB HB0]. change (vm_brk (m_vmmaps md)) with b in HB.
pose proof (lg_brk0 _ _ _ _ LG) as (B1 & B2 & B3 & B4 & B5).
pose proof (lg_placed _ _ _ _ LG r _ Hr eq_refl) as (Pal & Plo & Phi & Pimg). cbn [rg_len] in Phi, Pimg.
assert (P4 : PGSZ = 4096) by reflexivity.
assert (E4 : bv_unsigned (w64 PGSZ) = 4096) by reflexivity.
assert (Hb : bv_unsigned b = ly_reg L r + len) by lia.
pose proof (fresh_region b PGSZ ltac:(lia) ltac:(lia) ltac:(lia) Gfree) as FRG.
pose proof (fresh_entry b PGSZ ltac:(lia) ltac:(lia) ltac:(lia) Gfree) as FE.
pose proof (fresh_img b PGSZ ltac:(lia) ltac:(lia) ltac:(lia) Gfree) as FI.
pose proof (fun k => region_of_updk A A' r _ k ER) as RO. cbn beta in RO.
pose proof (region_of_lt _ _ _ Hr) as HrN.
assert (ROr : region_of A' r = Some (mkRegion RkBrk (len + PGSZ) [] true)).
{ rewrite RO, Nat.eqb_refl, (proj2 (Nat.ltb_lt _ _) HrN). reflexivity. }
assert (ROo : forall k, k <> r -> region_of A' k = region_of A k).
{ intros k Hk. rewrite RO. rewrite (proj2 (Nat.eqb_neq _ _) Hk). reflexivity. }
assert (ELB : live_bytes A' = live_bytes A + PGSZ).
{ rewrite (live_bytes_upd A A' r _ _ ER Hr eq_refl eq_refl). cbn. lia. }
assert (ENS : nslots A' = nslots A + 1).
{ rewrite (nslots_upd A A' r _ _ ER Hr). unfold region_slots. cbn [rg_live rg_kind rg_len]. rewrite Hlen, P4.
replace (4096 * p + 4096) with ((p + 1) * 4096) by lia. replace (4096 * p) with (p * 4096) by lia.
rewrite !Z.div_mul by lia. lia. }
pose proof live_bytes_nonneg' as LNN.
split.
- split; rewrite ?VM, ?VN, ?VR, ?VS, ?VB, ?VL, ?ELB, ?ENS, ?EB.
+ exact (lg_reserved _ _ _ _ LG).
+ exact (lg_limit _ _ _ _ LG).
+ intros k rg' Hk Hl Hkind. destruct (Nat.eq_dec k r) as [->|Hne]; [rewrite ROr in Hk; injection Hk as <-; exfalso; apply Hkind; reflexivity|].
rewrite (ROo k Hne) in Hk. right. exact (lg_maps _ _ _ _ LG k rg' Hk Hl Hkind).
+ intros k rg' off' Hk Hl Hkind Ha1 Ha2 Ha3 Hnin. destruct (Nat.eq_dec k r) as [->|Hne]; [rewrite ROr in Hk; injection Hk as <-; discriminate|].
rewrite (ROo k Hne) in Hk. destruct (lg_noaccess _ _ _ _ LG k rg' off' Hk Hl Hkind Ha1 Ha2 Ha3 Hnin) as [N1 N2].
split; [exact N1 | apply map_contains_cons'; exact N2].
+ exact (lg_brk0 _ _ _ _ LG).
+ split; [lia | exact HB0].
+ intros k rg' Hk Hl. destruct (Nat.eq_dec k r) as [->|Hne].
* rewrite ROr in Hk. injection Hk as <-. cbn [rg_len]. split; [exact Pal|]. split; [exact Plo|]. split; [lia|].
intros x Hx Himg. destruct (Z_lt_le_dec x (ly_reg L r + len)).
-- exact (Pimg x ltac:(lia) Himg).
-- exact (FI x Himg ltac:(lia)).
* rewrite (ROo k Hne) in Hk. exact (lg_placed _ _ _ _ LG k rg' Hk Hl).
+ cbn [length]. pose proof (lg_count _ _ _ _ LG) as CNT. rewrite Nat2Z.inj_succ. lia.
+ constructor.
* cbn [snd]. rewrite E4. lia.
* apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (lg_sizes _ _ _ _ LG) e He). cbn beta in *. lia.
+ pose proof (vm_backing_used_le_maps md' ML' MM') as VBK. rewrite VM in VBK. cbn [State.live_bytes] in VBK. rewrite E4 in VBK.
pose proof (lx_lb _ _ _ LX). lia.
+   rewrite VT. exact (lg_ceil _ _ _ _ LG).
- split; rewrite ?VM, ?ELB.
+ intros k rg' x Hk Hl Hx. destruct (Nat.eq_dec k r) as [->|Hne].
* rewrite ROr in Hk. injection Hk as <-. cbn [reg_lo rg_kind rg_len] in Hx.
destruct (Z_lt_le_dec x (ly_reg L r + len)).
-- destruct (lx_cov _ _ _ LX r _ x Hr eq_refl ltac:(cbn; lia)) as (e & He & Hex). exists e. split; [right; exact He | exact Hex].
-- exists (b, w64 PGSZ). split; [left; reflexivity|]. unfold iv_lo, iv_len. cbn [fst snd]. rewrite E4. lia.
* rewrite (ROo k Hne) in Hk. destruct (lx_cov _ _ _ LX k rg' x Hk Hl Hx) as (e & He & Hex). exists e. split; [right; exact He | exact Hex].
+ intros e [<- | He]; [| exact (lx_maps _ _ _ LX e He)]. unfold iv_lo, iv_len; cbn [fst snd]. rewrite E4. lia.
+ intros e1 e2 [<- | H1] [<- | H2].
* left. reflexivity.
* right. pose proof (FE e2 H2) as D. unfold iv_lo, iv_len in *; cbn [fst snd]. rewrite E4. exact D.
* right. pose proof (FE e1 H1) as D. unfold ranges_disjoint, iv_lo, iv_len in *; cbn [fst snd] in *. rewrite E4. lia.
* exact (lx_disj _ _ _ LX e1 e2 H1 H2).
+ intros k1 k2 rg1 rg2 Hne H1 H2 Hl1 Hl2 N1 N2.
destruct (Nat.eq_dec k1 r) as [->|Hne1]; destruct (Nat.eq_dec k2 r) as [->|Hne2].
* exfalso. exact (Hne eq_refl).
* rewrite ROr in H1. injection H1 as <-. rewrite (ROo k2 Hne2) in H2. cbn [reg_lo rg_kind rg_len] in *.
pose proof (lx_regs _ _ _ LX r k2 _ rg2 Hne Hr H2 eq_refl Hl2 ltac:(cbn; lia) N2) as D.
unfold ranges_disjoint in *. cbn [reg_lo rg_kind rg_len fst snd] in *.
pose proof (FRG k2 rg2 (ly_reg L k2 + reg_lo rg2) H2 Hl2 ltac:(lia)).
pose proof (FRG k2 rg2 (bv_unsigned b) H2 Hl2). lia.
* rewrite ROr in H2. injection H2 as <-. rewrite (ROo k1 Hne1) in H1. cbn [reg_lo rg_kind rg_len] in *.
pose proof (lx_regs _ _ _ LX k1 r rg1 _ Hne H1 Hr Hl1 eq_refl N1 ltac:(cbn; lia)) as D.
unfold ranges_disjoint in *. cbn [reg_lo rg_kind rg_len fst snd] in *.
pose proof (FRG k1 rg1 (ly_reg L k1 + reg_lo rg1) H1 Hl1 ltac:(lia)).
pose proof (FRG k1 rg1 (bv_unsigned b) H1 Hl1). lia.
* rewrite (ROo k1 Hne1) in H1. rewrite (ROo k2 Hne2) in H2. exact (lx_regs _ _ _ LX k1 k2 rg1 rg2 Hne H1 H2 Hl1 Hl2 N1 N2).
+ intros e [<- | He].
* exists r, (mkRegion RkBrk (len + PGSZ) [] true). split; [exact ROr|]. split; [reflexivity|].
unfold iv_lo, iv_len; cbn [fst snd rg_len]. rewrite E4. lia.
* destruct (lx_in _ _ _ LX e He) as (k & rg & Hk & Hl & G1 & G2).
destruct (Nat.eq_dec k r) as [->|Hnek].
-- rewrite Hr in Hk. injection Hk as <-. cbn [rg_len] in G2. exists r, (mkRegion RkBrk (len + PGSZ) [] true).
split; [exact ROr|]. split; [reflexivity|]. cbn [rg_len]. lia.
-- exists k, rg. rewrite (ROo k Hnek). auto.
+ cbn [State.live_bytes]. rewrite E4. pose proof (lx_lb _ _ _ LX). lia.
+
rewrite VN. intros e He. destruct (lx_noacc _ _ _ LX e He) as (E & HE & G1 & G2 & HR). exists E. split; [right; exact HE|].
split; [exact G1|]. split; [exact G2|]. intros k rg Hk Hl Hkd Hpos.
destruct (Nat.eq_dec k r) as [->|Hnek]; [rewrite ROr in Hk; injection Hk as <-; discriminate|].
rewrite (ROo k Hnek) in Hk. exact (HR k rg Hk Hl Hkd Hpos).
Qed.
Lemma ledger_new_brk : forall A' md3,
let h := m_vmmaps md in let b := vm_brk h in
st_brk A = BrkNever ->
region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (2 * PGSZ)) = true ->
st_regions A' = st_regions A ++ [mkRegion RkBrk (2 * PGSZ) [] true] -> st_brk A' = BrkCur N 2 ->
(vm_maps (m_vmmaps md3) = (b, w64 (2 * PGSZ)) :: vm_maps h \/
vm_maps (m_vmmaps md3) = (w64 (bv_unsigned b + PGSZ), w64 PGSZ) :: vm_maps h) ->
(forall lo n, 0 < bv_unsigned n ->
(bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + 2 * PGSZ <= bv_unsigned lo) ->
map_contains (vm_noaccess h) lo n = true -> map_contains (vm_noaccess (m_vmmaps md3)) lo n = true) ->
(forall e, In e (vm_noaccess (m_vmmaps md3)) ->
(exists e0, In e0 (vm_noaccess h) /\ iv_lo e0 <= iv_lo e /\ iv_lo e + iv_len e <= iv_lo e0 + iv_len e0) \/
(exists E, In E (vm_maps (m_vmmaps md3)) /\ iv_lo E <= iv_lo e /\ iv_lo e + iv_len e <= iv_lo E + iv_len E /\
bv_unsigned b <= iv_lo E /\ iv_lo E + iv_len E <= bv_unsigned b + 2 * PGSZ)) ->
vm_reserved (m_vmmaps md3) = vm_reserved h -> vm_start_brk (m_vmmaps md3) = vm_start_brk h ->
bv_unsigned (vm_brk (m_vmmaps md3)) = bv_unsigned b + 2 * PGSZ -> vm_limit (m_vmmaps md3) = vm_limit h ->
alloc_top (m_vmmaps md3) = alloc_top h ->
m_vm_lazy md3 = [] -> m_vm_materialized md3 = [] ->
ledger_ok B (Lset (bv_unsigned b)) A' md3 /\ ledger_x (Lset (bv_unsigned b)) A' md3.
Proof.
intros A' md3 h b Hbk Gfree ER EB VM VN VNX VR VS VB VL VT ML' MM'. subst h.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range b) as Ub.
pose proof (lg_brk _ _ _ _ LG) as HB. rewrite Hbk in HB. change (vm_brk (m_vmmaps md)) with b in HB.
pose proof (lg_brk0 _ _ _ _ LG) as (B1 & B2 & B3 & B4 & B5).
assert (P4 : PGSZ = 4096) by reflexivity.
assert (E8 : bv_unsigned (w64 (2 * PGSZ)) = 8192) by reflexivity.
assert (E4 : bv_unsigned (w64 PGSZ) = 4096) by reflexivity.
assert (Eb4 : bv_unsigned (w64 (bv_unsigned b + PGSZ)) = bv_unsigned b + 4096) by (unfold w64; rewrite u64_w64; lia).
pose proof (fresh_region b (2 * PGSZ) ltac:(lia) ltac:(lia) ltac:(lia) Gfree) as FRG.
pose proof (fresh_entry b (2 * PGSZ) ltac:(lia) ltac:(lia) ltac:(lia) Gfree) as FE.
pose proof (fresh_img b (2 * PGSZ) ltac:(lia) ltac:(lia) ltac:(lia) Gfree) as FI.
pose proof (fun k => region_of_new A A' _ k ER) as RO. cbn beta in RO. fold N in RO.
pose proof (live_bytes_new A A' _ ER eq_refl) as LB. cbn [rg_len] in LB.
pose proof (nslots_new A A' _ ER) as NS. unfold region_slots in NS. cbn [rg_live rg_kind rg_len] in NS.
replace (2 * PGSZ / PGSZ) with 2 in NS by reflexivity.
pose proof live_bytes_nonneg' as LNN.
assert (HEAD : exists e0, vm_maps (m_vmmaps md3) = e0 :: vm_maps (m_vmmaps md) /\
bv_unsigned b <= iv_lo e0 /\ iv_lo e0 <= bv_unsigned b + 4096 /\ iv_lo e0 + iv_len e0 = bv_unsigned b + 8192).
{ destruct VM as [VM|VM]; rewrite VM; eexists; (split; [reflexivity|]); unfold iv_lo, iv_len; cbn [fst snd]; rewrite ?E8, ?E4, ?Eb4; lia. }
destruct HEAD as ([e0a e0n] & VM0 & He0a & He0b & He0c). unfold iv_lo, iv_len in He0a, He0b, He0c. cbn [fst snd] in He0a, He0b, He0c.
split.
- split; rewrite ?VM0, ?VR, ?VS, ?VB, ?VL, ?LB, ?NS, ?EB.
+ exact (lg_reserved _ _ _ _ LG).
+ exact (lg_limit _ _ _ _ LG).
+ intros k rg Hk Hl Hkind. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
* right. rewrite (Lset_lt _ k H). exact (lg_maps _ _ _ _ LG k rg Hk Hl Hkind).
* destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. exfalso. apply Hkind. reflexivity.
+ intros k rg off Hk Hl Hkind Ho1 Ho2 Ho3 Hrw. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
* unfold w64 in *. rewrite (Lset_lt _ k H). destruct (lg_noaccess _ _ _ _ LG k rg off Hk Hl Hkind Ho1 Ho2 Ho3 Hrw) as [N1 N2].
pose proof (lg_placed _ _ _ _ LG k rg Hk Hl) as (_ & Klo & Khi & _).
split; [| apply map_contains_cons'; exact N2].
apply VN; [rewrite E4; lia | | exact N1].
rewrite u64_w64 by (unfold PGSZ in *; lia). rewrite E4.
pose proof (FRG k rg (ly_reg L k + off) Hk Hl ltac:(unfold reg_lo; rewrite Hkind; unfold PGSZ in *; lia)).
pose proof (FRG k rg (bv_unsigned b) Hk Hl).
assert (K : forall x, ly_reg L k + off <= x < ly_reg L k + off + 4096 -> ~ (bv_unsigned b <= x < bv_unsigned b + 2 * PGSZ)).
{ intros x Hx. apply (FRG k rg x Hk Hl). unfold reg_lo. rewrite Hkind. unfold PGSZ in *. lia. }
pose proof (K (ly_reg L k + off) ltac:(lia)). pose proof (K (ly_reg L k + off + 4095) ltac:(lia)).
destruct (Z_lt_le_dec (bv_unsigned b) (ly_reg L k + off)); unfold PGSZ in *; [|lia].
destruct (Z_lt_le_dec (ly_reg L k + off + 4095) (bv_unsigned b + 8192)); [|lia].
exfalso. apply (K (bv_unsigned b) ltac:(lia)). lia.
* destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. discriminate.
+ exact (lg_brk0 _ _ _ _ LG).
+ rewrite Lset_new. split; [unfold PGSZ in *; lia | cbn [Lset ly_brk0]; exact HB].
+ intros k rg Hk Hl. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
* rewrite (Lset_lt _ k H). exact (lg_placed _ _ _ _ LG k rg Hk Hl).
* destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. subst k. rewrite Lset_new. cbn [rg_len].
rewrite HB. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. intros x Hx Himg. rewrite <- HB in Hx. exact (FI x Himg Hx).
+ cbn [length]. pose proof (lg_count _ _ _ _ LG). rewrite Nat2Z.inj_succ. lia.
+ constructor.
* cbn [snd]. lia.
* apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (lg_sizes _ _ _ _ LG) e He). cbn beta in *. lia.
+ pose proof (vm_backing_used_le_maps md3 ML' MM') as VBK. rewrite VM0 in VBK. cbn [State.live_bytes] in VBK.
pose proof (lx_lb _ _ _ LX). lia.
+   rewrite VT. exact (lg_ceil _ _ _ _ LG).
- split; rewrite ?VM0, ?LB.
+ intros k rg x Hk Hl Hx. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
* rewrite (Lset_lt _ k H) in Hx. destruct (lx_cov _ _ _ LX k rg x Hk Hl Hx) as (e & He & Hex). exists e. split; [right; exact He | exact Hex].
* destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. subst k. rewrite Lset_new in Hx. cbn [reg_lo rg_kind rg_len] in Hx.
exists (e0a, e0n). split; [left; reflexivity|]. unfold iv_lo, iv_len. cbn [fst snd]. unfold PGSZ in *. lia.
+ intros e [<- | He]; [| exact (lx_maps _ _ _ LX e He)]. unfold iv_lo, iv_len. cbn [fst snd]. lia.
+ intros e1 e2 [<- | H1] [<- | H2].
* left. reflexivity.
* right. pose proof (FE e2 H2) as D. unfold ranges_disjoint, iv_lo, iv_len in *; cbn [fst snd] in *. unfold PGSZ in *. lia.
* right. pose proof (FE e1 H1) as D. unfold ranges_disjoint, iv_lo, iv_len in *; cbn [fst snd] in *. unfold PGSZ in *. lia.
* exact (lx_disj _ _ _ LX e1 e2 H1 H2).
+ intros k1 k2 rg1 rg2 Hne H1 H2 Hl1 Hl2 N1 N2. rewrite RO in H1, H2.
destruct (Nat.ltb_spec k1 N); destruct (Nat.ltb_spec k2 N).
* rewrite (Lset_lt _ k1 H), (Lset_lt _ k2 H0). exact (lx_regs _ _ _ LX k1 k2 rg1 rg2 Hne H1 H2 Hl1 Hl2 N1 N2).
* destruct (Nat.eqb_spec k2 N); [|discriminate]. injection H2 as <-. subst k2. rewrite (Lset_lt _ k1 H), Lset_new.
cbn [reg_lo rg_kind rg_len] in *. unfold ranges_disjoint; cbn [fst snd].
pose proof (FRG k1 rg1 (ly_reg L k1 + reg_lo rg1) H1 Hl1 ltac:(lia)).
pose proof (FRG k1 rg1 (bv_unsigned b + PGSZ) H1 Hl1). unfold PGSZ in *. lia.
* destruct (Nat.eqb_spec k1 N); [|discriminate]. injection H1 as <-. subst k1. rewrite (Lset_lt _ k2 H0), Lset_new.
cbn [reg_lo rg_kind rg_len] in *. unfold ranges_disjoint; cbn [fst snd].
pose proof (FRG k2 rg2 (ly_reg L k2 + reg_lo rg2) H2 Hl2 ltac:(lia)).
pose proof (FRG k2 rg2 (bv_unsigned b + PGSZ) H2 Hl2). unfold PGSZ in *. lia.
* destruct (Nat.eqb_spec k1 N); [|discriminate]. destruct (Nat.eqb_spec k2 N); [|discriminate]. exfalso. apply Hne. lia.
+ intros e [<- | He].
* exists N, (mkRegion RkBrk (2 * PGSZ) [] true). rewrite RO, Nat.ltb_irrefl, Nat.eqb_refl. split; [reflexivity|]. split; [reflexivity|].
rewrite Lset_new. unfold iv_lo, iv_len. cbn [rg_len fst snd]. unfold PGSZ in *. lia.
* destruct (lx_in _ _ _ LX e He) as (k & rg & Hk & Hl & G1 & G2). exists k, rg.
pose proof (region_of_lt _ _ _ Hk) as HkN. fold N in HkN.
rewrite RO. rewrite (proj2 (Nat.ltb_lt k N) HkN). rewrite (Lset_lt _ k HkN). auto.
+ cbn [State.live_bytes]. pose proof (lx_lb _ _ _ LX). unfold PGSZ in *. lia.
+
assert (RK : forall E k rg, rg_kind rg = RkMap ->
(region_of A k = Some rg -> rg_live rg = true -> ranges_disjoint (iv_lo E, iv_len E) (ly_reg L k, rg_len rg)) ->
region_of A' k = Some rg -> rg_live rg = true -> ranges_disjoint (iv_lo E, iv_len E) (ly_reg (Lset (bv_unsigned b)) k, rg_len rg)).
{ intros E k rg Hkd H Hk Hl. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
- rewrite (Lset_lt _ k H0). exact (H Hk Hl).
- destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. discriminate. }
intros e He. destruct (VNX e He) as [(e0 & He0 & S1 & S2) | (E & HE & S1 & S2 & N1 & N2)].
* destruct (lx_noacc _ _ _ LX e0 He0) as (E & HE & G1 & G2 & HR). exists E. split; [first [apply in_cons; exact HE | exact HE]|].
split; [lia|]. split; [lia|]. intros k rg Hk Hl Hkd Hpos. apply (RK _ k rg Hkd); [| exact Hk | exact Hl].
intros Hk0 Hl0. exact (HR k rg Hk0 Hl0 Hkd Hpos).
* exists E. split; [rewrite VM0 in HE; exact HE|]. split; [exact S1|]. split; [exact S2|].
intros k rg Hk Hl Hkd Hpos. apply (RK _ k rg Hkd); [| exact Hk | exact Hl]. intros Hk0 Hl0.
unfold ranges_disjoint; cbn [fst snd].
pose proof (FRG k rg (ly_reg L k) Hk0 Hl0 ltac:(unfold reg_lo; rewrite Hkd; lia)).
pose proof (FRG k rg (bv_unsigned b) Hk0 Hl0) as F2. unfold reg_lo in F2. rewrite Hkd in F2. cbn in F2. unfold PGSZ in *. lia.
Qed.
End Ev.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
