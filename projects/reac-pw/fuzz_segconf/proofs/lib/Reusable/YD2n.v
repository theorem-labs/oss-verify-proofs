(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD2n.v, with its module paths changed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG0k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Inductive md3 := MA | MB | MAB.
Definition join (a b : md3) : md3 :=
match a, b with MA, MA => MA | MB, MB => MB | _, _ => MAB end.
Definition mle (a b : md3) : Prop := a = b \/ b = MAB.
Definition iskernel (q : kreq) : bool := match q with KDepot _ => false | _ => true end.
Section e.
Context {R : Type}.
Variable L : R -> md3 -> Prop.
Inductive tmg : md3 -> itree astate R -> Prop :=
| tmg_ret : forall r m, L r m -> tmg m (IRet r)
| tmg_fail : forall m f, tmg m (IFail f)
| tmg_kspin : forall m q snap (k : Z -> itree astate R),
iskernel q = true -> tmg m (k 1) ->
(forall z, aok snap q z -> aGranted z = false -> is_spin (k z) = true) ->
tmg m (IAsk q snap k)
| tmg_kref : forall m0 m1 q snap (k : Z -> itree astate R),
iskernel q = true -> krefusable q = true -> tmg m1 (k 1) ->
(forall z, aok snap q z -> aGranted z = false -> tmg m0 (k z)) ->
tmg (join m0 m1) (IAsk q snap k)
| tmg_depot : forall m tr snap k, (forall z, aok snap (KDepot tr) z -> tmg m (k z)) -> tmg m (IAsk (KDepot tr) snap k).
End e.
Arguments tmg {R} L m t.
Definition Lmal (r : sptr * astate) (m : md3) : Prop := (fst r = PNull /\ m = MA) \/ (fst r <> PNull /\ m = MB).
Definition tm : md3 -> itree astate (sptr * astate) -> Prop := tmg Lmal.
Lemma tmg_ibind {A B} (LB : B -> md3 -> Prop) :
forall (t : itree astate A) (K : A -> itree astate B) m,
tmg (fun a m' => tmg LB m' (K a)) m t -> tmg LB m (ibind t K).
Proof.
induction t as [a | q snap k IH | pc | f]; intros K m H; cbn.
- inversion H; subst. assumption.
- inversion H as [| | m' q' snap' k' KQ T1 SP | m0 m1 q' snap' k' KQ RQ T1 T0 | m' tr snap' k' TD]; subst.
+ apply (tmg_kspin LB m q snap (fun z => ibind (k z) K) KQ (IH 1 K m T1)).
intros z Hz Hg. specialize (SP z Hz Hg). destruct (k z); try discriminate SP. reflexivity.
+ apply (tmg_kref LB m0 m1 q snap (fun z => ibind (k z) K) KQ RQ (IH 1 K m1 T1)).
intros z Hz Hg. exact (IH z K m0 (T0 z Hz Hg)).
+ apply tmg_depot. intros z Hz. exact (IH z K m (TD z Hz)).
- inversion H.
- apply tmg_fail.
Qed.
Definition tmM {A} (LA : A * astate -> md3 -> Prop) (m : md3) (c : M A) (s : astate) : Prop := tmg LA m (c s).
Lemma tmM_bind {A B} (LB : B * astate -> md3 -> Prop) :
forall (c : M A) (k : A -> M B) m s,
tmg (fun r m' => tmg LB m' (k (fst r) (snd r))) m (c s) -> tmg LB m (bind c k s).
Proof.
intros c k m s H. unfold bind. apply tmg_ibind. revert H. generalize (c s). intros t H. induction H.
- apply tmg_ret. destruct r as [a s']. exact H.
- apply tmg_fail.
- apply tmg_kspin; assumption.
- apply tmg_kref; assumption.
- apply tmg_depot. assumption.
Qed.
Lemma tmg_mono {A} (LA LA' : A -> md3 -> Prop) : forall m t, (forall a m, LA a m -> LA' a m) -> tmg LA m t -> tmg LA' m t.
Proof.
intros m t HL H. induction H.
- apply tmg_ret. apply HL. exact H.
- apply tmg_fail.
- apply tmg_kspin; assumption.
- apply tmg_kref; assumption.
- apply tmg_depot. assumption.
Qed.
Lemma tmg_leaf {A} (LA : A -> md3 -> Prop) : forall a m, LA a m -> tmg LA m (IRet a). Proof. intros; apply tmg_ret; assumption. Qed.
Lemma tmM_ret {A} (LA : A * astate -> md3 -> Prop) : forall a s m, LA (a, s) m -> tmg LA m (ret a s).
Proof. intros; apply tmg_ret; assumption. Qed.
Lemma tmM_mcheck (LA : unit * astate -> md3 -> Prop) : forall b pc s m, LA (tt, s) m -> tmg LA m (mcheck b pc s).
Proof. intros b pc s m H. unfold mcheck. destruct b; [apply tmg_ret; exact H | apply tmg_fail]. Qed.
Local Open Scope am_scope.
Definition malloc_tail (n : Z) (trace : list Z) (beg : sptr) : M sptr :=
depot_put trace ;;
(let k := mkChunk beg n CAllocated in
(if needs_remap (ck_n k) then
z <- askz (KShadowRemap (ck_user k) (8 * (ck_n k / 8))) ;;
if aGranted z then ret tt else spin 449860
else ret tt) ;;
modify (fun s => set_chunks (upd_chunk (st_chunks s) k) s) ;;
ret (ck_user k)).
Lemma malloc_unfold : forall n trace S,
n < kMaxAllowedMalloc - kPage ->
malloc n trace S =
bind (if from_primary n
then (fun s => bind (cache_alloc (chunk_class n)) (fun o => ret (match o with Some off => Some (PPrim off) | None => None end)) s)
else sec_alloc n)
(fun ob => match ob with None => ret PNull | Some beg => malloc_tail n trace beg end)
(set_nev (st_nev S + 1) S).
Proof.
intros n trace S Hn. unfold malloc, malloc_tail, tick, mcheck.
replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; exact Hn).
reflexivity.
Qed.
Lemma padd_nonnull : forall beg d, beg <> PNull -> padd beg d <> PNull.
Proof. intros [| | |] d H; cbn; try congruence; discriminate. Qed.
Lemma depot_put_tm (LA : unit * astate -> md3 -> Prop) : forall trace s m,
(forall s', LA (tt, s') m) -> tmg LA m (depot_put trace s).
Proof.
intros trace s m HL. unfold depot_put, bind, askz. cbn [ibind].
apply tmg_depot. intros z Hz. cbn [ibind].
destruct (z =? 0); cbn [ibind ret get mcheck put].
- apply tmg_ret. apply HL.
- unfold mcheck. destruct (depot_ids s + 1 <? kDepotIdsPerBlock); cbn [ibind ret fail]; [| apply tmg_fail].
destruct (kStartFramesMax + depot_frames s + Z.of_nat (length trace) + 1 <? kStoreFramesPerBlock); cbn [ibind ret fail put]; [| apply tmg_fail].
apply tmg_ret. apply HL.
Qed.
Lemma malloc_tail_tm : forall n trace beg s, beg <> PNull -> tm MB (malloc_tail n trace beg s).
Proof.
intros n trace beg s Hbeg. unfold malloc_tail.
apply tmM_bind. apply depot_put_tm. intros s'. cbn [fst snd].
apply tmM_bind.
destruct (needs_remap (ck_n (mkChunk beg n CAllocated))).
- unfold bind, askz, ret, spin. cbn [ibind].
apply (tmg_kspin _ MB); [reflexivity | |].
+ cbn [aGranted Z.eqb Pos.eqb ibind fst snd]. unfold modify, ret. cbn [ibind]. apply tmg_ret. cbn [fst snd].
apply tmg_ret. right. split; [| reflexivity]. cbn [fst]. apply padd_nonnull. exact Hbeg.
+ intros z Hz Hg. rewrite Hg. reflexivity.
- unfold ret. apply tmg_ret. cbn [fst snd]. apply tmM_bind. unfold modify. apply tmg_ret. cbn [fst snd].
apply tmg_ret. right. split; [| reflexivity]. cbn [fst]. apply padd_nonnull. exact Hbeg.
Qed.
Lemma sec_alloc_tm : forall n s,
tmg (fun r m => match fst r with None => m = MA | Some beg => beg <> PNull /\ m = MB end) MAB (sec_alloc n s).
Proof.
intros n s. unfold sec_alloc, bind, askz. cbn [ibind].
change MAB with (join MA MB). apply (tmg_kref _ MA MB); [reflexivity | reflexivity | |].
-
cbn [Z.eqb ibind get]. unfold mcheck.
destruct (Z.of_nat (length (st_sec_arr s)) <? kMaxNumChunks); cbn [ibind ret fail put]; [| apply tmg_fail].
destruct (Z.of_nat (length (st_sec_arr s)) =? st_sec_reserved s).
+ unfold askz. cbn [ibind]. apply (tmg_kspin _ MB); [reflexivity | |].
* cbn [aGranted Z.eqb ibind modify ret]. apply tmg_ret. cbn [fst]. split; [discriminate | reflexivity].
* intros z Hz Hg. rewrite Hg. reflexivity.
+ cbn [ibind ret modify]. apply tmg_ret. cbn [fst]. split; [discriminate | reflexivity].
- intros z Hz Hg. cbn in Hz. destruct Hz as [-> | ->]; [| discriminate Hg].
cbn [Z.eqb ibind ret]. apply tmg_ret. reflexivity.
Qed.
Theorem malloc_tm_sec : forall n trace S,
from_primary n = false -> n < kMaxAllowedMalloc - kPage -> tm MAB (malloc n trace S).
Proof.
intros n trace S Hp Hn. unfold tm. rewrite (malloc_unfold n trace S Hn), Hp.
apply tmM_bind. eapply tmg_mono; [| exact (sec_alloc_tm n _)].
intros [ob s'] m Hm. cbn [fst snd] in Hm |- *. destruct ob as [beg|].
- destruct Hm as [Hbeg ->]. apply malloc_tail_tm. exact Hbeg.
- subst m. apply tmg_ret. left. split; reflexivity.
Qed.
Lemma tm_get_region (Q : region * astate -> md3 -> Prop) : forall c s m, Q (reg s c, s) m -> tmg Q m (get_region c s).
Proof. intros c s m H. unfold get_region, bind, get, ret. cbn [ibind]. apply tmg_ret. exact H. Qed.
Lemma tm_set_region (Q : unit * astate -> md3 -> Prop) : forall c r s m, Q (tt, upd_reg c r s) m -> tmg Q m (set_region c r s).
Proof. intros c r s m H. unfold set_region, modify. apply tmg_ret. exact H. Qed.
Lemma tm_get_pc (Q : pclass * astate -> md3 -> Prop) : forall c s m, Q (cache s c, s) m -> tmg Q m (get_pc c s).
Proof. intros c s m H. unfold get_pc, bind, get, ret. cbn [ibind]. apply tmg_ret. exact H. Qed.
Lemma tm_set_pc (Q : unit * astate -> md3 -> Prop) : forall c p s m, Q (tt, upd_pc c p s) m -> tmg Q m (set_pc c p s).
Proof. intros c p s m H. unfold set_pc, modify. apply tmg_ret. exact H. Qed.
Lemma tm_get (Q : astate * astate -> md3 -> Prop) : forall s m, Q (s, s) m -> tmg Q m (get s).
Proof. intros s m H. apply tmg_ret. exact H. Qed.
Lemma tm_put (Q : unit * astate -> md3 -> Prop) : forall s' s m, Q (tt, s') m -> tmg Q m (put s' s).
Proof. intros s' s m H. apply tmg_ret. exact H. Qed.
Lemma tm_bind_ret {A B} (Q : B * astate -> md3 -> Prop) : forall (a : A) (k : A -> M B) s m, tmg Q m (k a s) -> tmg Q m (bind (ret a) k s).
Proof. intros a k s m H. exact H. Qed.
Lemma tm_bind_fail {A B} (Q : B * astate -> md3 -> Prop) : forall f (k : A -> M B) s m, tmg Q m (bind (fail f) k s).
Proof. intros f k s m. apply tmg_fail. Qed.
Lemma tm_askz_kref {B} (Q : B * astate -> md3 -> Prop) : forall q (k : Z -> M B) s m0 m1,
iskernel q = true -> krefusable q = true -> tmg Q m1 (k 1 s) ->
(forall z, aok s q z -> aGranted z = false -> tmg Q m0 (k z s)) -> tmg Q (join m0 m1) (bind (askz q) k s).
Proof. intros q k s m0 m1 KQ RQ H1 H0. unfold bind, askz. cbn [ibind]. apply tmg_kref; assumption. Qed.
Definition ca_pop (c : Z) : M (option Z) :=
p <- get_pc c ;;
match pc_chunks p with
| [] => ret None
| l => let off := last l 0 in
set_pc c (mkPC (pc_max p) (removelast l)) ;;
ret (Some (region_off c + off))
end.
Definition ca_rest (c : Z) : M (option Z) := refill_if_empty c ;; ca_pop c.
Lemma cache_alloc_eq : forall c, cache_alloc c = (init_cache_if_needed ;; ca_rest c).
Proof. reflexivity. Qed.
Definition Lca (r : option Z * astate) (m : md3) : Prop := match fst r with None => m = MA | Some _ => m = MB end.
Section g.
Variables (c : Z) (s1 : astate).
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hsz : 0 < class_size c <= kMaxSize.
Hypothesis LR : length (st_regions s1) = 32%nat.
Hypothesis M0 : rg_mapped_user (reg s1 c) = 0.
Hypothesis A0 : rg_alloc_user (reg s1 c) = 0.
Hypothesis F0 : rg_free (reg s1 c) = [].
#[local] Notation mm := (max_cached c / 2).
#[local] Notation NN := (kUserMapSize / class_size c).
Lemma MC : 1 <= mm <= 8.
Proof.
unfold max_cached. rewrite (Z.mul_comm 2), Z.div_mul by lia.
pose proof (Z.div_pos 1024 (class_size c) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma NS : 1 <= mm * class_size c <= kUserMapSize.
Proof.
pose proof MC. unfold max_cached in *. rewrite (Z.mul_comm 2), Z.div_mul in * by lia.
unfold kUserMapSize, kMaxSize in *.
destruct (Z_lt_le_dec 1024 (class_size c)).
- rewrite (Z.div_small 1024 (class_size c)) in * by lia. change (Z.max 1 (Z.min 8 0)) with 1. lia.
- assert (1 <= 1024 / class_size c) by (apply Z.div_le_lower_bound; lia).
pose proof (Z.mul_div_le 1024 (class_size c) ltac:(lia)). nia.
Qed.
Lemma MN : mm <= NN /\ 1 <= NN.
Proof.
pose proof NS. pose proof MC. split; [apply Z.div_le_lower_bound; lia|].
apply Z.div_le_lower_bound; [lia|]. unfold kUserMapSize, kMaxSize in *. lia.
Qed.
Lemma ca_rest_tm : forall s2,
st_regions s2 = st_regions s1 -> length (st_cache s2) = 32%nat ->
pc_chunks (cache s2 c) = [] -> pc_max (cache s2 c) = max_cached c ->
tmg Lca MAB (ca_rest c s2).
Proof.
intros s2 R2 L2 C2 X2. pose proof MC as HMC. pose proof NS as HNS. pose proof MN as [HMN HN1].
remember mm as m eqn:Em in *. remember NN as N eqn:EN in *.
assert (LR2 : length (st_regions s2) = 32%nat) by (rewrite R2; exact LR).
assert (RG2 : reg s2 c = reg s1 c) by (unfold reg; rewrite R2; reflexivity).
unfold ca_rest. apply tmM_bind. unfold refill_if_empty. apply tmM_bind. apply tm_get_pc. cbn [fst snd].
rewrite C2, X2, <- Em.
apply tmM_bind. unfold get_from_allocator. apply tmM_bind. apply tm_get_region. cbn [fst snd].
rewrite RG2, F0. cbn [fa_len]. replace (0 <? m) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Z.sub_0_r.
apply tmM_bind.
match goal with |- tmg ?L _ _ =>
assert (PF : forall s', st_cache s' = st_cache s2 -> L (false, s') MA);
[| assert (PT : forall s' fa ho, st_cache s' = st_cache s2 -> length (st_regions s') = 32%nat ->
reg s' c = mkRegion kUserMapSize (N * class_size c) fa [FRun 0 N] ho -> L (true, s') MB)] end.
{ intros s' HC'. cbn [fst snd negb]. apply tmg_ret. cbn [fst snd]. apply tmg_ret. cbn [fst snd].
unfold ca_pop. apply tmM_bind. apply tm_get_pc. cbn [fst snd].
replace (cache s' c) with (cache s2 c) by (unfold cache; rewrite HC'; reflexivity). rewrite C2. apply tmg_ret. reflexivity. }
{ intros s' fa ho HC' LR' RG'. cbn [fst snd negb]. apply tmM_bind. apply tm_get_region. cbn [fst snd]. rewrite RG'. cbn [rg_free fa_len].
replace (N + 0 <? m) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (fa_pop_n 10000 (class_size c) m [FRun 0 N] []) as [[tops rest]|] eqn:EP; [| apply tmg_fail].
assert (RO : runs_ok [FRun 0 N]) by (constructor; [cbv beta iota; exact HN1 | constructor]).
destruct (fa_pop_n_spec 10000%nat (class_size c) m [FRun 0 N] [] tops rest RO ltac:(lia) EP) as (_ & _ & _ & LT). cbn [length] in LT.
cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_holes].
apply tmM_bind. apply tm_set_region. cbn [fst snd]. apply tmg_ret. cbn [fst snd].
apply tm_set_pc. cbn [fst snd].
unfold ca_pop. apply tmM_bind. apply tm_get_pc. cbn [fst snd].
rewrite cache_upd_pc; [| lia | unfold upd_reg, set_regions; cbn [st_cache]; rewrite HC', L2; lia]. cbn [pc_chunks pc_max]. unfold cache_fill_order.
destruct (rev tops) as [|z l] eqn:ER; [apply (f_equal (@length Z)) in ER; rewrite length_rev in ER; cbn in ER; lia|].
apply tmM_bind. apply tm_set_pc. cbn [fst snd]. apply tmg_ret. reflexivity. }
unfold populate. apply tmM_bind. unfold map_more_user. apply tmM_bind. apply tm_get_region. cbn [fst snd].
rewrite RG2, M0, A0. replace (0 <? 0 + m * class_size c) with true by (symmetry; apply Z.ltb_lt; lia).
replace (round_up (0 + m * class_size c - 0) kUserMapSize) with kUserMapSize.
2:{ unfold round_up, kUserMapSize in *. replace ((0 + m * class_size c - 0 + 262144 - 1) / 262144) with 1; [reflexivity|].
apply Z.div_unique with (r := m * class_size c - 1); lia. }
unfold mcheck. replace (0 + kUserMapSize <=? kFreeArrayOffset) with true by reflexivity. apply tm_bind_ret.
rewrite F0.
match goal with |- tmg ?L _ (bind (askz ?q) ?K ?s) =>
assert (RF : forall z, aok s q z -> aGranted z = false -> tmg L MA (K z s));
[| assert (GR : forall m1, (if 4 * N <=? rg_mapped_fa (reg s1 c) then m1 = MB else m1 = MAB) -> tmg L m1 (K 1 s))] end.
{ intros z Hz Hg. cbn beta. rewrite Hg. cbn [fst snd].
apply tmM_bind. destruct (aDestroyed z); [apply tm_set_region | apply tmg_ret]; cbn [fst snd]; apply tmg_ret;
cbn [fst snd negb]; apply tmg_ret; apply PF; reflexivity. }
{ intros m1 Hm1. cbn [aGranted Z.eqb Pos.eqb].
apply tmM_bind. apply tm_set_region. cbn [fst snd]. apply tmg_ret. cbn [fst snd negb].
apply tmM_bind. apply tm_get_region. cbn [fst snd]. rewrite reg_upd_reg by lia.
cbn [rg_mapped_user rg_alloc_user rg_free rg_mapped_fa rg_holes fa_len].
replace (0 + kUserMapSize - 0) with kUserMapSize by lia. rewrite <- EN.
apply tmM_bind.
match goal with |- tmg ?L2 _ _ =>
assert (PF2 : forall s', st_cache s' = st_cache s2 -> L2 (false, s') MA);
[| assert (PT2 : forall s' fa ho, st_cache s' = st_cache s2 -> length (st_regions s') = 32%nat ->
reg s' c = mkRegion kUserMapSize 0 fa [] ho -> L2 (true, s') MB)] end.
{ intros s' HC'. cbn [fst snd negb]. apply tmg_ret. apply PF. exact HC'. }
{ intros s' fa ho HC' LR' RG'. cbn [fst snd negb]. apply tmM_bind. apply tm_get_region. cbn [fst snd]. rewrite RG'.
cbn [rg_mapped_user rg_alloc_user rg_free rg_mapped_fa rg_holes].
apply tmM_bind. apply tm_set_region. cbn [fst snd]. apply tmg_ret. apply (PT _ fa ho).
- unfold upd_reg, set_regions. cbn [st_cache]. exact HC'.
- unfold upd_reg, set_regions. cbn [st_regions]. rewrite zupd_length. exact LR'.
- rewrite reg_upd_reg by lia. rewrite Z.add_0_l. reflexivity. }
unfold ensure_free_array. apply tmM_bind. apply tm_get_region. cbn [fst snd]. rewrite reg_upd_reg by lia.
cbn [rg_mapped_user rg_alloc_user rg_free rg_mapped_fa rg_holes]. replace (0 + N) with N by lia.
destruct (4 * N <=? rg_mapped_fa (reg s1 c)) eqn:EFA; subst m1.
- apply tmg_ret. apply (PT2 _ (rg_mapped_fa (reg s1 c)) (del_hole 0 (rg_holes (reg s1 c)))); [reflexivity | | rewrite reg_upd_reg by lia; reflexivity].
unfold upd_reg, set_regions. cbn [st_regions]. rewrite zupd_length. exact LR2.
- unfold mcheck. destruct (round_up (4 * N) kFreeArrayMapSize <=? kFreeArrayMax); [apply tm_bind_ret | apply tm_bind_fail].
change MAB with (join MA MB). apply tm_askz_kref; [reflexivity | reflexivity | |].
+ cbn [aGranted Z.eqb Pos.eqb]. apply tmM_bind. apply tm_set_region. cbn [fst snd]. apply tmg_ret.
eapply PT2; [reflexivity | | rewrite reg_upd_reg; [reflexivity | lia |]].
* unfold upd_reg, set_regions. cbn [st_regions]. rewrite !zupd_length. exact LR2.
* unfold upd_reg, set_regions. cbn [st_regions]. rewrite !zupd_length. lia.
+ intros z Hz Hg. cbn beta. rewrite Hg. cbn [fst snd].
apply tmM_bind. destruct (aDestroyed z); [apply tm_set_region | apply tmg_ret]; cbn [fst snd]; apply tmg_ret; apply PF2; reflexivity. }
destruct (4 * N <=? rg_mapped_fa (reg s1 c));
[change MAB with (join MA MB) | change MAB with (join MA MAB)];
(apply tm_askz_kref; [reflexivity | reflexivity | apply GR; reflexivity | exact RF]).
Qed.
Hypothesis LC : length (st_cache s1) = 32%nat.
Hypothesis C0 : pc_chunks (cache s1 c) = [].
Hypothesis XC : st_cache_inited s1 = true -> pc_max (cache s1 c) = max_cached c.
Lemma cache_alloc_tm : tmg Lca MAB (cache_alloc c s1).
Proof.
rewrite cache_alloc_eq. apply tmM_bind. unfold init_cache_if_needed. apply tmM_bind. apply tm_get. cbn [fst snd].
destruct (st_cache_inited s1) eqn:CI.
- apply tmg_ret. cbn [fst snd]. apply ca_rest_tm; [reflexivity | exact LC | exact C0 | exact (XC eq_refl)].
- apply tm_put. cbn [fst snd]. apply ca_rest_tm.
+ reflexivity.
+ cbn [st_cache set_cache_inited set_cache]. apply length_init_caches.
+ rewrite cache_after_init by lia. cbn [pc_chunks]. exact C0.
+ rewrite cache_after_init by lia. reflexivity.
Qed.
End g.
Definition malloc_shape_pre (n : Z) (S : astate) : Prop :=
from_primary n = true -> exists cs, prim_pristine_except S cs /\ ~ In (chunk_class n) cs.
Theorem malloc_tm_prim : forall U n trc S cs,
Wf U S -> prim_pristine_except S cs -> 0 <= n -> n < kMaxAllowedMalloc - kPage -> from_primary n = true ->
~ In (chunk_class n) cs -> tm MAB (malloc n trc S).
Proof.
intros U n trc S cs W HP Hn0 Hn Hp Hcs.
pose proof (primary_geometry n Hn0 Hp) as (Hc & _ & Hsz & _ & Hpos).
set (c := chunk_class n) in *.
destruct (HP c ltac:(lia) Hcs) as (M0 & A0 & F0 & C0).
pose proof (wf_len_regions _ _ _ _ _ W) as LR. pose proof (wf_len_cache _ _ _ _ _ W) as LC.
pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c ltac:(lia))) as XC. unfold cache in XC.
unfold tm. rewrite (malloc_unfold n trc S Hn), Hp.
apply tmM_bind. cbn beta. apply tmM_bind.
eapply tmg_mono; [| apply (cache_alloc_tm c (set_nev (st_nev S + 1) S)); try assumption; try lia].
- intros [o s'] m Hm. unfold Lca in Hm. cbn [fst snd] in Hm. apply tmg_ret. cbn [fst snd]. destruct o as [off|]; subst m.
+ apply malloc_tail_tm. discriminate.
+ apply tmg_ret. left. split; reflexivity.
- intros CI. cbn [set_nev st_cache_inited] in CI. rewrite CI in XC. exact (proj1 XC).
Qed.
Theorem malloc_tm_shape : forall U n trc S,
Wf U S -> 0 <= n < MALLOC_MAX -> malloc_shape_pre n S -> tm MAB (malloc n trc S).
Proof.
intros U n trc S W Hn Hpre.
assert (Hmax : n < kMaxAllowedMalloc - kPage) by (unfold MALLOC_MAX, kMaxAllowedMalloc, kPage in *; lia).
destruct (from_primary n) eqn:Hp.
- destruct (Hpre Hp) as (cs & HP & Hcs). exact (malloc_tm_prim U n trc S cs W HP ltac:(lia) Hmax Hp Hcs).
- exact (malloc_tm_sec n trc S Hp Hmax).
Qed.
Lemma malloc_shape_pre_sec : forall n S, from_primary n = false -> malloc_shape_pre n S.
Proof. intros n S Hp Hp'. congruence. Qed.
Lemma malloc_shape_pre_pristine : forall n S cs,
prim_pristine_except S cs -> (from_primary n = true -> ~ In (chunk_class n) cs) -> malloc_shape_pre n S.
Proof. intros n S cs HP Hcs Hp. exists cs. split; [exact HP | exact (Hcs Hp)]. Qed.
